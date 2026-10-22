/* Burn Pile – online server. No dependencies: `node server.js` (PORT env var optional).
   The server is the referee: it runs engine.js, validates every move, runs AI seats, and sends each
   player ONLY what they may see (E.publicView). Updates go out over Server-Sent Events; moves come in via POST. */
'use strict';
const http = require('http'), fs = require('fs'), path = require('path'), crypto = require('crypto');
const E = require('./engine.js'), AI = require('./ai.js');
const PORT = process.env.PORT || 3000;
const FILES = { '/': 'home.html', '/home.html': 'home.html', '/local.html': 'local.html', '/online.html': 'online.html' };
const AINAMES = ['Ava', 'Ben', 'Cleo', 'Dev', 'Eli', 'Fay'];
const rooms = new Map();

const token = () => crypto.randomBytes(16).toString('hex');
function newCode() {
  let c;
  do { c = Array.from({ length: 4 }, () => 'ABCDEFGHJKLMNPQRSTUVWXYZ'[crypto.randomInt(24)]).join(''); } while (rooms.has(c));
  return c;
}
const clean = s => String(s || '').replace(/[<>&"'`]/g, '').trim().slice(0, 16);

/* ---------- rooms & lobby ---------- */
function makeRoom(hostName) {
  const code = newCode(), t = token();
  const room = { code, n: 4, cfg: { diff: 'normal', pers: 'mixed', aiMs: process.env.BP_FAST === '1' ? 5 : 1600 }, seats: Array(4).fill(null), members: new Map(),
    host: t, phase: 'lobby', st: null, seq: 0, anim: null, timer: null, last: Date.now() };
  room.members.set(t, { token: t, name: clean(hostName) || 'Host', seat: null, res: null, offline: null });
  rooms.set(code, room);
  return { room, token: t };
}
function addMember(room, name) {
  let base = clean(name) || 'Player', nm = base, k = 2;
  const taken = n => [...room.members.values()].some(m => m.name === n);
  while (taken(nm)) nm = base + k++;
  const t = token();
  room.members.set(t, { token: t, name: nm, seat: null, res: null, offline: null });
  return t;
}
function lobbyView(room, m) {
  return { type: 'lobby', code: room.code, n: room.n, cfg: room.cfg, host: m.token === room.host, you: { name: m.name, seat: m.seat },
    seats: room.seats.map((s, i) => s ? { taken: true, name: room.members.get(s).name, mine: s === m.token } : { taken: false }),
    members: [...room.members.values()].map(x => ({ name: x.name, seat: x.seat, host: x.token === room.host, online: !!x.res })) };
}
function gameView(room, m) {
  const st = room.st;
  if (m.seat === null) return { type: 'spectate', code: room.code, members: room.members.size };
  const v = E.publicView(st, m.seat), p = st.players[m.seat];
  v.type = 'game'; v.code = room.code; v.n = st.players.length;
  v.log = st.log.slice(-60); v.loser = st.loser; v.adjudicated = st.adjudicated; v.host = m.token === room.host;
  v.ready = st.players.map(q => q.ready);
  v.zone = E.zoneOf(st, p);
  v.moves = st.phase === 'play' && st.current === m.seat ? E.getLegalMoves(st, m.seat) : [];
  v.legalRanks = E.legalRanks(st);
  v.anim = room.anim;
  return v;
}
function send(m, v) { if (m.res) { try { m.res.write('event: state\ndata: ' + JSON.stringify(v) + '\n\n'); } catch (e) { /* closed */ } } }
function broadcast(room) {
  room.last = Date.now();
  for (const m of room.members.values()) send(m, room.phase === 'lobby' ? lobbyView(room, m) : gameView(room, m));
}

/* ---------- game flow ---------- */
function startGame(room) {
  const n = room.n, humans = room.seats.map(s => !!s);
  const names = room.seats.map((s, i) => s ? room.members.get(s).name : AINAMES[i]);
  const personalities = humans.map((h, i) => h ? null : (room.cfg.pers === 'mixed' ? AI.PERS[i % 3] : room.cfg.pers));
  const st = E.newGame({ players: n, names, controllers: humans.map(h => h ? 'human' : 'ai'), personalities });
  st.players.forEach(p => { if (p.controller === 'ai') E.act(st, p.index, AI.decide(st, p.index, { difficulty: room.cfg.diff }).action); });
  room.st = st; room.phase = 'game'; room.anim = null; room.seq = 0;
  for (const m of room.members.values()) if (m.seat === null) m.seat = null;
  broadcast(room); schedule(room);
}
const ALLOWED = new Set(['play', 'pickup', 'flip', 'faceUp']);
function sanitize(a) {
  if (!a || !ALLOWED.has(a.type)) return null;
  const o = { type: a.type };
  if (Array.isArray(a.ids)) o.ids = a.ids.filter(Number.isInteger).slice(0, 60);
  if (Number.isInteger(a.id)) o.id = a.id;
  if (typeof a.asRank === 'string') o.asRank = a.asRank.slice(0, 3);
  if (a.direction === 'cw' || a.direction === 'ccw') o.direction = a.direction;
  if (Number.isInteger(a.target)) o.target = a.target;
  return o;
}
function perform(room, seat, rawAction) {
  const st = room.st, a = sanitize(rawAction);
  if (!a) return { ok: false, error: 'Bad action.' };
  const prevPile = st.pile.map(c => ({ ...c })), wasSetup = st.phase === 'setup';
  const r = E.act(st, seat, a, {});
  if (!r.ok) return r;
  if (wasSetup) room.anim = null;
  else {
    const played = {};
    for (const e of r.events || []) if (e.type === 'play') for (const id of e.cards) {
      const c = st.pile.find(x => x.id === id) || st.burned.find(x => x.id === id);
      if (c) played[id] = { ...c };
    }
    room.anim = { seq: ++room.seq, events: r.events || [], prevPile, played };
  }
  if (st.phase === 'over') room.phase = 'over';
  broadcast(room); schedule(room);
  return { ok: true };
}
function schedule(room) {
  clearTimeout(room.timer);
  const st = room.st;
  if (!st || st.phase !== 'play') return;
  const p = st.players[st.current];
  const away = p.controller === 'human' && !seatOnline(room, p.index);
  if (p.controller !== 'ai' && !away) return;
  const mem = room.members.get(room.seats[p.index]);   // an absent human gets a 6s grace period (page reload), then the AI plays at normal pace
  const delay = p.controller === 'ai' ? room.cfg.aiMs : Math.max(room.cfg.aiMs, 6000 - (Date.now() - ((mem && mem.offline) || Date.now())));
  room.timer = setTimeout(() => aiMove(room), delay);
}
const seatOnline = (room, seat) => { const t = room.seats[seat]; const m = t && room.members.get(t); return !!(m && m.res); };
function aiMove(room) {
  const st = room.st;
  if (!st || st.phase !== 'play') return;
  const pi = st.current, d = AI.decide(st, pi, { difficulty: room.cfg.diff });
  const r = perform(room, pi, d.action);
  if (!r.ok) perform(room, pi, { type: 'pickup' });
}

/* ---------- HTTP ---------- */
function body(req) {
  return new Promise(res => {
    let s = '';
    req.on('data', d => { s += d; if (s.length > 1e5) req.destroy(); });
    req.on('end', () => { try { res(JSON.parse(s || '{}')); } catch (e) { res({}); } });
  });
}
const json = (res, o, code = 200) => { res.writeHead(code, { 'Content-Type': 'application/json' }); res.end(JSON.stringify(o)); };
function member(b) { const room = rooms.get(String(b.room || '').toUpperCase()); const m = room && room.members.get(b.token); return { room, m }; }

async function api(req, res, name) {
  const b = await body(req);
  if (name === 'create') { const { room, token: t } = makeRoom(b.name); return json(res, { ok: true, room: room.code, token: t }); }
  if (name === 'join') {
    const room = rooms.get(String(b.room || '').toUpperCase());
    if (!room) return json(res, { ok: false, error: 'Room not found.' });
    if (room.phase !== 'lobby') return json(res, { ok: false, error: 'That game has already started.' });
    if (room.members.size >= 12) return json(res, { ok: false, error: 'Room is full.' });
    return json(res, { ok: true, room: room.code, token: addMember(room, b.name) });
  }
  const { room, m } = member(b);
  if (!room || !m) return json(res, { ok: false, error: 'Unknown room or player.' }, 404);
  const host = m.token === room.host;
  switch (name) {
    case 'hello': return json(res, { ok: true });
    case 'seat': {
      if (room.phase !== 'lobby') return json(res, { ok: false, error: 'Game already started.' });
      const s = b.seat;
      if (s === null || s === -1) { if (m.seat !== null) { room.seats[m.seat] = null; m.seat = null; } }
      else {
        if (!Number.isInteger(s) || s < 0 || s >= room.n) return json(res, { ok: false, error: 'No such seat.' });
        if (room.seats[s] && room.seats[s] !== m.token) return json(res, { ok: false, error: 'That seat is taken.' });
        if (m.seat !== null) room.seats[m.seat] = null;
        room.seats[s] = m.token; m.seat = s;
      }
      broadcast(room); return json(res, { ok: true });
    }
    case 'config': {
      if (!host || room.phase !== 'lobby') return json(res, { ok: false, error: 'Only the host can change settings.' });
      if (Number.isInteger(b.n) && b.n >= 2 && b.n <= 6 && b.n !== room.n) {
        room.n = b.n; const old = room.seats;
        room.seats = Array.from({ length: b.n }, (_, i) => old[i] || null);
        for (let i = b.n; i < old.length; i++) if (old[i]) room.members.get(old[i]).seat = null;
      }
      if (['easy', 'normal', 'hard'].includes(b.diff)) room.cfg.diff = b.diff;
      if (['mixed', ...AI.PERS].includes(b.pers)) room.cfg.pers = b.pers;
      if ([900, 1600, 2400].includes(b.aiMs) && process.env.BP_FAST !== '1') room.cfg.aiMs = b.aiMs;
      broadcast(room); return json(res, { ok: true });
    }
    case 'start':
      if (!host || room.phase !== 'lobby') return json(res, { ok: false, error: 'Only the host can start.' });
      if (!room.seats.some(Boolean)) return json(res, { ok: false, error: 'Someone must take a seat first.' });
      startGame(room); return json(res, { ok: true });
    case 'act':
      if (room.phase !== 'game' || !room.st) return json(res, { ok: false, error: 'No game running.' });
      if (m.seat === null) return json(res, { ok: false, error: 'You are not seated.' });
      return json(res, perform(room, m.seat, b.action));
    case 'rematch':
      if (!host || room.phase !== 'over') return json(res, { ok: false, error: 'Only the host can start a rematch, after the game ends.' });
      clearTimeout(room.timer); room.st = null; room.anim = null; room.phase = 'lobby'; broadcast(room); return json(res, { ok: true });
    case 'leave': {
      if (m.seat !== null && room.phase === 'lobby') room.seats[m.seat] = null;
      if (m.res) { try { m.res.end(); } catch (e) { /* ignore */ } }
      if (room.phase === 'lobby') { room.members.delete(m.token); if (host) { const next = room.members.values().next().value; if (next) room.host = next.token; else rooms.delete(room.code); } }
      else m.offline = Date.now();
      if (rooms.has(room.code)) broadcast(room);
      return json(res, { ok: true });
    }
    default: return json(res, { ok: false, error: 'Unknown call.' }, 404);
  }
}
function events(req, res, url) {
  const room = rooms.get(String(url.searchParams.get('room') || '').toUpperCase()), m = room && room.members.get(url.searchParams.get('token'));
  if (!room || !m) { res.writeHead(404); return res.end(); }
  res.writeHead(200, { 'Content-Type': 'text/event-stream', 'Cache-Control': 'no-cache, no-transform', Connection: 'keep-alive', 'X-Accel-Buffering': 'no' });
  res.write('retry: 2000\n\n');
  if (m.res) { try { m.res.end(); } catch (e) { /* replaced */ } }
  m.res = res; m.offline = null;
  const ping = setInterval(() => { try { res.write(': ping\n\n'); } catch (e) { /* closed */ } }, 15000);
  send(m, room.phase === 'lobby' ? lobbyView(room, m) : gameView(room, m));
  broadcast(room);   // others see you come online
  req.on('close', () => {
    clearInterval(ping);
    if (m.res === res) { m.res = null; m.offline = Date.now(); if (rooms.has(room.code)) { broadcast(room); schedule(room); } }
  });
}
const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, 'http://x');
  try {
    if (req.method === 'POST' && url.pathname.startsWith('/api/')) return await api(req, res, url.pathname.slice(5));
    if (req.method === 'GET' && url.pathname === '/events') return events(req, res, url);
    if (req.method === 'GET' && FILES[url.pathname]) {
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' });
      return res.end(fs.readFileSync(path.join(__dirname, FILES[url.pathname])));
    }
    res.writeHead(404); res.end('Not found');
  } catch (e) { console.error(e); try { res.writeHead(500); res.end('Server error'); } catch (x) { /* ignore */ } }
});
// housekeeping: drop lobby members who stayed offline, and stale rooms
setInterval(() => {
  const now = Date.now();
  for (const [code, room] of rooms) {
    if (room.phase === 'lobby') for (const [t, m] of room.members) if (!m.res && m.offline && now - m.offline > 20000) {
      if (m.seat !== null) room.seats[m.seat] = null;
      room.members.delete(t);
      if (t === room.host) { const next = room.members.values().next().value; if (next) room.host = next.token; }
      broadcast(room);
    }
    const anyOnline = [...room.members.values()].some(m => m.res);
    if (room.members.size === 0 || (!anyOnline && now - room.last > 3 * 3600e3) || now - room.last > 12 * 3600e3) { clearTimeout(room.timer); rooms.delete(code); }
  }
}, 10000).unref();
if (require.main === module) server.listen(PORT, () => console.log('Burn Pile online server on http://localhost:' + PORT));
module.exports = { server, rooms };
