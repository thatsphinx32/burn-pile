/* AI players. Decisions use only: own cards, public table information (E.publicView), and the engine's
   own legal-move generator. Opponents' hands, anyone's face-down cards and the draw order are never read. */
(function (root) {
'use strict';
const E = (typeof module !== 'undefined' && module.exports && typeof require === 'function') ? require('./engine.js') : root.CardEngine;
const PERS = ['conservative', 'aggressive', 'tactical'];
// How much a card is worth holding on to (specials are valuable).
const KEEP = { '4': 1, '5': 1.5, '6': .5, '7': 3, '8': 3, '9': .5, '10': 6, J: 1.5, Q: 2, K: 3, '3': 5, '2': 6, A: 5, JOKER: 9 };
const left = p => p.handCount + p.faceUp.length + p.faceDownCount;
const danger = p => { const n = left(p); return n <= 2 ? 3 : n <= 4 ? 1.5 : 0; };   // how close an opponent is to finishing

function nextOf(v, from, dir) {
  const n = v.players.length;
  for (let i = 1; i < n; i++) { const j = ((from + dir * i) % n + n) % n; if (!v.players[j].finished) return j; }
  return null;
}
function run(v, rank) {   // length of the run of `rank` on top of the pile (3s are transparent, except when counting 3s)
  let c = 0;
  for (let i = v.pile.length - 1; i >= 0; i--) {
    const a = v.pile[i].as;
    if (rank === '3') { if (a === '3') c++; else break; }
    else { if (a === '3') continue; if (a === rank) c++; else break; }
  }
  return c;
}
const burns = (v, m) => m.rank === '10' || run(v, m.rank) + m.count >= 4;
function after(v, m) {    // pile state the next player will face after this move
  if (burns(v, m) || m.rank === '2') return { effRank: null, restriction: null };
  if (m.rank === '3') return { effRank: v.effRank, restriction: v.restriction };
  return { effRank: m.rank, restriction: m.rank === '5' ? 'face' : m.rank === '7' ? 'low' : null };
}
// Only certain when the opponent has no hand left: their face-up cards are public.
function cannotPlay(pseudo, p) {
  if (p.handCount === 0 && p.faceUp.length) return !p.faceUp.some(c => c.rank === 'JOKER' || E.rankAllowed(pseudo, c.rank));
  return false;
}

function score(v, me, m, P, diff, pool) {
  const mp = v.players[me], cards = m.ids.map(id => pool[id]);
  const keep = cards.reduce((s, c) => s + KEEP[c.rank], 0), r = m.rank;
  const B = burns(v, m), aft = after(v, m), dir = v.direction;
  const nx = nextOf(v, me, dir), np = nx === null ? null : v.players[nx], dn = np ? danger(np) : 0;
  const stuck = !B && np ? cannotPlay(aft, np) : false;
  const W = { conservative: [2.2, 1.4, .7], aggressive: [4, .5, .1], tactical: [3, .8, .35] }[P] || [2.2, 1.4, .7]; // [shed, keep-cost, rank-cost]
  const urg = Math.min(1, Math.max(0, (mp.handCount - 5) / 8));            // big hand: stop hoarding specials, shed and reset
  let s = W[0] * m.count * (1 + urg) - W[1] * keep * (1 - .8 * urg) - W[2] * E.STR[r] * (1 - .8 * urg);
  const bad = c => c.rank === '6' || c.rank === '9' || c.rank === 'JOKER';           // these can never be the last card played
  const nBad = cards.filter(bad).length;
  if (nBad && left(mp) > m.count) s += nBad * (left(mp) <= 6 ? 3.5 : r === 'JOKER' ? 0 : 1.5);   // dump them while others can still follow
  if (B) s += .4 * v.pile.length + (P === 'aggressive' ? 9 : P === 'tactical' ? (v.pile.length >= 5 ? 6 : 3) : (v.pile.length >= 5 ? 4 : 1.5));
  if (r === '8') s += P === 'aggressive' ? 3 : P === 'tactical' ? .5 + 2.5 * dn : 0;
  if (r === '8' && v.players.filter(p => !p.finished).length === 2) s += 2.5;       // heads-up: an 8 is an extra turn
  if (r === '4' && v.players.length > 2) {
    const pv = nextOf(v, me, -dir), dp = pv === null ? 0 : danger(v.players[pv]);
    s += P === 'tactical' ? 2 * (dn - dp) : P === 'aggressive' ? 1 : -.5;
  }
  if (r === '7') s += P === 'aggressive' ? 3 : P === 'tactical' ? 1 + 1.5 * dn : -1;
  if (r === '5') s += P === 'aggressive' ? 1.5 : P === 'tactical' ? .5 : 0;
  if (r === 'A' && !B) s += P === 'aggressive' ? 3 : P === 'tactical' ? 2.5 : .5;
  if (r === '2' && !B && P === 'tactical' && dn >= 1.5) s -= 2.5 * dn;              // don't hand a near-winner a free reset
  if (stuck) s += P === 'tactical' ? 4 : P === 'aggressive' ? 3 : (diff === 'hard' ? 1.5 : 0);
  if (mp.faceDownCount === 0) {                                                       // don't get stranded holding only 6/9/Joker
    const rest = Object.values(pool).filter(c => !m.ids.includes(c.id));
    if (rest.length && rest.every(bad)) s -= 10;
  }
  return s;
}

function pickTarget(v, me, P, rng = Math.random) {   // who plays after my Ace
  const opp = v.players.filter(p => !p.finished && p.index !== me);
  if (!opp.length) return undefined;
  const tie = () => rng() - .5;
  if (P === 'conservative') return opp.slice().sort((a, b) => left(b) - left(a) || tie())[0].index;   // hand the turn to the least dangerous player
  const wild = p => p.faceUp.some(c => c.rank === 'JOKER' || E.WILD.has(c.rank));
  const sureStuck = p => P === 'tactical' && p.handCount === 0 && p.faceUp.length > 0 && !wild(p);       // after an Ace only wilds are playable
  return opp.slice().sort((a, b) => (sureStuck(b) - sureStuck(a)) || (left(a) - left(b)) || tie())[0].index; // target the leader
}
function pickDir(v, me, P, rng = Math.random) {      // only used for the opening 4♣
  if (P === 'tactical') {
    const a = nextOf(v, me, 1), b = nextOf(v, me, -1);
    if (a !== null && b !== null) return left(v.players[a]) >= left(v.players[b]) ? 'cw' : 'ccw';
  }
  return rng() < .5 ? 'cw' : 'ccw';
}
function pickFaceUp(hand, P, diff, rng = Math.random) {
  const f = {
    conservative: c => ['2', '3', '10', 'JOKER'].includes(c.rank) ? -5 + E.STR[c.rank] * .1 : E.STR[c.rank],   // keep specials in hand
    aggressive: c => ({ A: 10, '10': 9, K: 8, Q: 7, J: 6, '2': 5 }[c.rank] ?? E.STR[c.rank] * .4) - (c.rank === 'JOKER' ? 9 : 0),
    tactical: c => { let x = E.STR[c.rank]; if (c.rank === '6' || c.rank === '9') x -= 4; if (c.rank === 'JOKER') x = -6; if (c.rank === '2' || c.rank === '3') x -= 3; return x; },
  }[P] || (c => E.STR[c.rank]);
  const noise = diff === 'easy' ? 5 : diff === 'hard' ? .1 : .6;
  return hand.map(c => [c, f(c) + (rng() - .5) * 2 * noise]).sort((a, b) => b[1] - a[1]).slice(0, 3).map(x => x[0].id);
}

/* Returns { action, opts } ready for E.act(st, pi, action, opts). */
function decide(st, pi, o = {}) {
  const rng = o.rng || Math.random, diff = o.difficulty || 'normal';
  const v = E.publicView(st, pi), me = v.players[pi], P = me.personality || 'conservative';
  if (st.phase === 'setup') return { action: { type: 'faceUp', ids: pickFaceUp(me.hand, P, diff, rng) } };
  if (E.zoneOf(st, st.players[pi]) === 'faceDown')      // blind: slot ids only, never the cards
    return { action: { type: 'flip', id: me.faceDownIds[Math.floor(rng() * me.faceDownIds.length)] }, opts: { chooseJoker: r => r.includes('10') ? '10' : r[0] } };
  const moves = E.getLegalMoves(st, pi);
  if (!moves.length) return { action: { type: 'pickup' } };
  let best;
  if (rng() < (o.explore ?? ({ easy: .3, normal: .06, hard: .04 }[diff] ?? .06))) best = moves[Math.floor(rng() * moves.length)];   // occasional off-script move also breaks cycles
  else {
    const noise = { easy: 6, normal: .8, hard: .2 }[diff] ?? .8, pool = {};
    me.hand.concat(me.faceUp).forEach(c => pool[c.id] = c);
    let bs = -1e9;
    for (const m of moves) { const s = score(v, pi, m, P, diff, pool) + (rng() - .5) * 2 * noise; if (s > bs) { bs = s; best = m; } }
  }
  return { action: { type: 'play', ids: best.ids, asRank: best.asRank, direction: pickDir(v, pi, P, rng), target: pickTarget(v, pi, P, rng) } };
}

const API = { PERS, decide, pickTarget, pickFaceUp, pickDir };
if (typeof module !== 'undefined' && module.exports) module.exports = API; else root.AI = API;
})(typeof window !== 'undefined' ? window : globalThis);
