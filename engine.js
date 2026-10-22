/* Card-shedding game rules engine. No DOM. Works in browser (window.CardEngine) and Node. */
(function (root) {
'use strict';

const RANKS = ['4','5','6','7','8','9','10','J','Q','K','3','2','A','JOKER']; // low -> high (custom hierarchy)
const PLAIN = RANKS.slice(0, 13);
const STR = {}; RANKS.forEach((r, i) => STR[r] = i);
const WILD = new Set(['2','3','10','A']);   // playable on anything (subject to restrictions)
const FACE = new Set(['J','Q','K']);
const LOW = new Set(['4','5','6','7']);
const SUITS = ['S','H','D','C'];
const NO_FINISH = new Set(['6','9','JOKER']);
const MAX_TURNS = 1500;
const LABEL = { J:'Jack', Q:'Queen', K:'King', A:'Ace', JOKER:'Joker' };
const NUMW = ['','a','two','three','four','five','six','seven','eight'];

function mulberry32(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
function createDeck(jokers = 2) {
  const cards = []; let id = 0;
  for (const s of SUITS) for (const r of PLAIN) cards.push({ id: id++, rank: r, suit: s });
  for (let i = 0; i < jokers; i++) cards.push({ id: id++, rank: 'JOKER', suit: null });
  return cards;
}
function shuffle(arr, rng = Math.random) {
  for (let i = arr.length - 1; i > 0; i--) { const j = Math.floor(rng() * (i + 1)); [arr[i], arr[j]] = [arr[j], arr[i]]; }
  return arr;
}
// Cards per hand at deal time; always leaves a draw pile of >= `reserve` cards when possible.
// No-refill rules deal the whole deck, so pick the smallest joker count (>= 2) that divides evenly.
function autoJokers(n) { for (let j = 2; j < 2 + n; j++) if ((52 + j) % n === 0) return j; return 2; }
function handSizeFor(n, total, reserve = 6) {
  return Math.max(1, Math.min(10, Math.floor((total - reserve) / n) - 6));
}
const cardsLeft = p => p.hand.length + p.faceUp.length + p.faceDown.length;
const log = (s, t) => { s.log.push(t); if (s.log.length > 300) s.log.shift(); };
const rl = (r, n) => (LABEL[r] || r) + (n > 1 ? 's' : '');
const describe = (n, r) => n === 1 ? `${r === 'A' || r === '8' ? 'an' : 'a'} ${LABEL[r] || r}` : `${NUMW[n] || n} ${rl(r, n)}`;

/* ---------- setup ---------- */
function newGame(o = {}) {
  const n = o.players || 4;
  if (n < 2 || n > 6) throw new Error('2-6 players');
  const rng = o.rng || Math.random;
  const refill = !!o.refill;      // optional legacy rule: refill hand to 3 from a draw pile (off by default)
  const deck = shuffle(createDeck(o.jokers ?? (refill ? 2 : autoJokers(n))), rng);
  const total = deck.length;
  { const perm = shuffle([...Array(total).keys()], rng); deck.forEach((c, i) => { c.id = perm[i]; }); }   // ids carry no information about the card (needed for online play)
  const handSize = refill ? handSizeFor(n, total) : Math.max(1, Math.floor(total / n) - 6);
  const st = { rng, total, handSize, refill, players: [], drawPile: deck, pile: [], burned: [], current: 0, direction: 1,
    effRank: null, restriction: null, finishOrder: [], log: [], phase: 'setup', opening: false, openZone: null,
    passCount: 0, turns: 0, seen: {}, loser: null, adjudicated: null, events: [] };
  for (let i = 0; i < n; i++) st.players.push({
    index: i, name: (o.names && o.names[i]) || `Player ${i + 1}`,
    controller: (o.controllers && o.controllers[i]) || (i === 0 ? 'human' : 'ai'),
    personality: (o.personalities && o.personalities[i]) || null,
    hand: [], faceUp: [], faceDown: [], finished: false, place: null, ready: false });
  for (const p of st.players) for (let k = 0; k < 3; k++) p.faceDown.push(deck.pop());   // dealt blind
  for (const p of st.players) for (let k = 0; k < 3 + handSize; k++) p.hand.push(deck.pop()); // pool to pick face-ups from
  if (!refill && deck.length) st.burned.push(...deck.splice(0));   // only if an explicit joker count doesn't divide evenly
  log(st, refill ? `New game: ${n} players, ${deck.length} cards in the draw pile.` : `New game: ${n} players, ${total} cards dealt to everyone.`);
  return st;
}
function chooseFaceUp(st, pi, ids) {
  if (st.phase !== 'setup') return err('Not in setup');
  const p = st.players[pi];
  if (!p || p.ready) return err('Already chosen');
  if (!Array.isArray(ids) || ids.length !== 3 || new Set(ids).size !== 3) return err('Pick exactly 3 cards');
  const picked = ids.map(id => p.hand.find(c => c.id === id));
  if (picked.some(c => !c)) return err('Card not in your hand');
  p.hand = p.hand.filter(c => !picked.includes(c));
  p.faceUp = picked; p.ready = true;
  if (st.players.every(q => q.ready)) beginPlay(st);
  return { ok: true };
}
const isOpenCard = c => c.rank === '4' && c.suit === 'C';
function beginPlay(st) {
  st.phase = 'play';
  for (const zone of ['hand', 'faceUp']) for (const p of st.players) if (p[zone].some(isOpenCard)) {
    st.current = p.index; st.opening = true; st.openZone = zone;
    log(st, `${p.name} holds the 4 of clubs and opens the game.`);
    return;
  }
  st.current = Math.floor(st.rng() * st.players.length);
  log(st, `The 4 of clubs is hidden. ${st.players[st.current].name} starts.`);
}

/* ---------- rules ---------- */
function rankAllowed(st, r) {
  if (st.restriction === 'low') return LOW.has(r) || r === '10' || r === '2' || r === '3'; // 7: default ranking (2..7 are <= 7); 10 and 3 playable on anything
  if (st.restriction === 'face' && FACE.has(r)) return false;        // 5: no J/Q/K
  if (st.effRank === null || WILD.has(r)) return true;
  return STR[r] >= STR[st.effRank];
}
function whyBlocked(st, r) {
  if (st.restriction === 'low') return 'A 7 is in force: play lower than 7 (7 is ok) or a 10.';
  if (st.restriction === 'face' && FACE.has(r)) return 'A 5 is in force: no Jacks, Queens or Kings.';
  if (r === '5' && FACE.has(st.effRank)) return 'A 5 cannot be played on a Jack, Queen or King.';
  return `Must play ${LABEL[st.effRank] || st.effRank} or higher (or a 2, 3, 10 or Ace).`;
}
function legalRanks(st) { return PLAIN.filter(r => rankAllowed(st, r)); }
function zoneOf(st, p) {
  if (st.opening && st.current === p.index) return st.openZone;
  if (p.hand.length) return 'hand';
  if (p.faceUp.length) return 'faceUp';
  if (p.faceDown.length) return 'faceDown';
  return null;
}
function validateMove(st, pi, ids, asRank) {
  const fail = (reason, extra) => Object.assign({ ok: false, reason }, extra);
  const p = st.players[pi];
  if (st.phase !== 'play') return fail('The game is not in play.');
  if (!p || p.finished || st.current !== pi) return fail('Not your turn.');
  if (!Array.isArray(ids) || !ids.length || new Set(ids).size !== ids.length) return fail('Select at least one card.');
  const zone = zoneOf(st, p);
  if (!zone) return fail('No cards to play.');
  if (zone === 'faceDown' && ids.length !== 1) return fail('Face-down cards are played one at a time.');
  const cards = ids.map(id => p[zone].find(c => c.id === id));
  if (cards.some(c => !c)) return fail('Those cards are not currently playable.');
  const real = cards.filter(c => c.rank !== 'JOKER'), jokers = cards.length - real.length;
  let rank;
  if (real.length) {
    rank = real[0].rank;
    if (real.some(c => c.rank !== rank)) return fail('Only cards of the same rank can be played together.');
    if (jokers && asRank && asRank !== rank) return fail('A Joker played with other cards must match their rank.');
  } else {
    rank = asRank || '10';
    if (!PLAIN.includes(rank)) return fail('Invalid Joker identity.');
  }
  if (st.opening && !cards.some(isOpenCard)) return fail('The opening play must include the 4 of clubs.');
  if (!rankAllowed(st, rank)) return fail(whyBlocked(st, rank));
  const total = cardsLeft(p);
  if (cards.length === total && cards.some(c => NO_FINISH.has(c.rank)))
    return fail('You cannot finish with a 6, a 9 or a Joker.', { forcedPickup: true });
  return { ok: true, cards, rank, zone };
}
function getLegalMoves(st, pi) {
  const p = st.players[pi];
  if (st.phase !== 'play' || !p || p.finished || st.current !== pi) return [];
  const zone = zoneOf(st, p);
  if (!zone || zone === 'faceDown') return [];
  const cards = p[zone], jokers = cards.filter(c => c.rank === 'JOKER'), by = {};
  cards.filter(c => c.rank !== 'JOKER').forEach(c => (by[c.rank] = by[c.rank] || []).push(c));
  const moves = [];
  const consider = (sel, as) => {
    const v = validateMove(st, pi, sel.map(c => c.id), as);
    if (v.ok) moves.push({ ids: sel.map(c => c.id), asRank: v.rank, rank: v.rank, count: sel.length, jokers: sel.filter(c => c.rank === 'JOKER').length });
  };
  for (const r of Object.keys(by)) {
    const g = by[r].slice().sort((a, b) => isOpenCard(b) - isOpenCard(a));
    for (let k = 1; k <= g.length; k++) for (let m = 0; m <= jokers.length; m++) consider(g.slice(0, k).concat(jokers.slice(0, m)), r);
  }
  for (const r of PLAIN) for (let m = 1; m <= jokers.length; m++) consider(jokers.slice(0, m), r);
  return moves;
}
function fourOfKind(st) {   // 3s are transparent for other ranks, but four 3s in a row burn
  let n3 = 0;
  for (let i = st.pile.length - 1; i >= 0 && st.pile[i].as === '3'; i--) n3++;
  if (n3 >= 4) return '3';
  let r = null, n = 0;
  for (let i = st.pile.length - 1; i >= 0; i--) {
    const a = st.pile[i].as;
    if (a === '3') continue;
    if (r === null) { r = a; n = 1; } else if (a === r) n++; else break;
  }
  return n >= 4 ? r : null;
}
function wouldBurn(st, m) {   // would playing move `m` (from getLegalMoves) burn the pile?
  if (m.rank === '10') return true;
  let c = 0;
  for (let i = st.pile.length - 1; i >= 0; i--) {
    const a = st.pile[i].as;
    if (m.rank === '3') { if (a === '3') c++; else break; }
    else { if (a === '3') continue; if (a === m.rank) c++; else break; }
  }
  return c + m.count >= 4;
}
function nextEligible(st, from, dir) {
  const n = st.players.length;
  for (let i = 1; i < n; i++) { const idx = ((from + dir * i) % n + n) % n; if (!st.players[idx].finished) return idx; }
  return null;
}
function stepAhead(st, from, skips) {
  let cur = from;
  for (let k = 0; k <= skips; k++) {
    const nx = nextEligible(st, cur, st.direction);
    if (nx === null) return null;
    if (k < skips) log(st, `${st.players[nx].name} was skipped.`);
    cur = nx;
  }
  return cur;
}
function refill(st, p) { const d = []; while (p.hand.length < 3 && st.drawPile.length) { const c = st.drawPile.pop(); p.hand.push(c); d.push(c.id); } return d; }
function burnPile(st, why, p) {
  const n = st.pile.length;
  st.burned.push(...st.pile); st.pile = [];
  st.effRank = null; st.restriction = null;
  st.events.push({ type: 'burn', player: p.index, count: n, why });
  log(st, `The pile (${n} cards) was burned by ${why}.`);
}
function checkFinished(st, p) {
  if (!p.finished && cardsLeft(p) === 0) {
    p.finished = true; st.finishOrder.push(p.index); p.place = st.finishOrder.length;
    st.events.push({ type: 'finish', player: p.index });
    log(st, `${p.name} has finished (place ${p.place}).`);
  }
}
function endGame(st) {
  const left = st.players.filter(p => !p.finished);
  st.phase = 'over';
  if (left.length === 1) { const l = left[0]; st.loser = l.index; l.place = st.players.length; st.finishOrder.push(l.index); log(st, `${l.name} is the last player with cards and loses.`); }
}
function signature(st) {   // position fingerprint, used to detect endless cycles
  const z = p => [p.hand, p.faceUp, p.faceDown].map(a => a.map(c => c.rank).sort().join('')).join('|');
  return [st.current, st.direction, st.effRank, st.restriction, st.drawPile.length, st.pile.map(c => c.as).join(''),
    st.players.map(p => p.finished ? 'x' : z(p)).join('/')].join('#');
}
function adjudicate(st, why) {
  const left = st.players.filter(p => !p.finished).sort((a, b) => cardsLeft(a) - cardsLeft(b));
  left.slice(0, -1).forEach(p => { p.finished = true; st.finishOrder.push(p.index); p.place = st.finishOrder.length; });
  st.adjudicated = why; log(st, `Game stalled (${why}); fewest cards wins.`);
  endGame(st);
}
function applyPlay(st, p, v, opts) {
  const { cards, rank, zone } = v;
  const wasOpening = st.opening;
  p[zone] = p[zone].filter(c => !cards.includes(c));
  cards.forEach(c => { c.as = rank; st.pile.push(c); });
  const jk = cards.some(c => c.rank === 'JOKER');
  st.events.push({ type: 'play', player: p.index, cards: cards.map(c => c.id), rank, zone });
  log(st, `${p.name} played ${describe(cards.length, rank)}${jk ? ' (using a Joker)' : ''}${zone === 'faceUp' ? ' from their face-up cards' : zone === 'faceDown' ? ' from a face-down card' : ''}.`);
  st.passCount = 0;
  if (rank === '3') { /* invisible: rank and restriction unchanged */ }
  else if (rank === '2') { st.effRank = null; st.restriction = null; }
  else { st.effRank = rank; st.restriction = rank === '5' ? 'face' : rank === '7' ? 'low' : null; }
  if (wasOpening) {
    st.opening = false; st.openZone = null;
    st.direction = opts.direction === 'ccw' ? -1 : 1;
    log(st, `${p.name} chose ${st.direction === 1 ? 'clockwise' : 'anticlockwise'} play.`);
  } else if (rank === '4' && st.players.length > 2) {
    st.direction *= -1; st.events.push({ type: 'reverse' }); log(st, `${p.name} reversed the direction.`);   // any number of 4s = one reversal
  }
  const skips = rank === '8' ? 1 : 0;   // any number of 8s skips exactly one player
  if (zone === 'hand' && st.refill) { const d = refill(st, p); if (d.length) st.events.push({ type: 'draw', player: p.index, cards: d, count: d.length }); }
  let burn = null;
  if (rank === '10') burn = 'a 10';
  else { const f = fourOfKind(st); if (f) burn = `four matching ${rl(f, 2)}`; }
  checkFinished(st, p);
  if (burn) burnPile(st, burn, p);
  if (st.players.filter(q => !q.finished).length <= 1) { endGame(st); return; }
  let next;
  if (burn && !p.finished) { next = p.index; log(st, `${p.name} takes another turn.`); }
  else if (rank === 'A') {
    let t = opts.target;
    if (!(Number.isInteger(t) && t !== p.index && st.players[t] && !st.players[t].finished)) t = nextEligible(st, p.index, st.direction);
    next = t; log(st, `${p.name} played an Ace and selected ${st.players[t].name}.`);
  } else next = stepAhead(st, p.index, burn ? 0 : skips);
  st.current = next;
}
function doPickup(st, p, note) {
  const n = st.pile.length;
  st.pile.forEach(c => delete c.as);
  p.hand.push(...st.pile); st.pile = [];
  st.effRank = null; st.restriction = null;
  st.events.push({ type: 'pickup', player: p.index, count: n });
  if (n) { st.passCount = 0; log(st, `${p.name} ${note ? note + ' and ' : ''}picked up ${n} card${n > 1 ? 's' : ''}.`); }
  else { st.passCount++; log(st, `${p.name} ${note || 'had no playable card'} and passed.`); }
  st.current = stepAhead(st, p.index, 0);
}
const err = reason => ({ ok: false, error: reason });

/* ---------- public entry point: every human/AI action goes through here ---------- */
function act(st, pi, action, opts = {}) {
  st.events = [];
  if (st.phase === 'setup') return action.type === 'faceUp' ? chooseFaceUp(st, pi, action.ids) : err('Choose your face-up cards first.');
  if (st.phase !== 'play') return err('The game is over.');
  const p = st.players[pi];
  if (!p || p.finished || st.current !== pi) return err('Not your turn.');
  if (action.type === 'play') {
    const v = validateMove(st, pi, action.ids, action.asRank);
    if (!v.ok) {
      if (!v.forcedPickup) return err(v.reason);
      doPickup(st, p, 'tried to finish with a 6, 9 or Joker');
    } else applyPlay(st, p, v, action);
  } else if (action.type === 'pickup') {
    const zone = zoneOf(st, p);
    if (zone === 'faceDown') return err('Choose a face-down card to play.');
    if (st.opening) return err('You must open with the 4 of clubs.');
    if (getLegalMoves(st, pi).length) return err('You have a playable card.');
    doPickup(st, p, st.pile.length ? 'had no legal move' : null);
  } else if (action.type === 'flip') {
    if (zoneOf(st, p) !== 'faceDown') return err('Face-down cards are not in play yet.');
    const card = p.faceDown.find(c => c.id === action.id);
    if (!card) return err('No such face-down card.');
    st.events.push({ type: 'reveal', player: p.index, card: { ...card } });
    let as;
    if (card.rank === 'JOKER') {
      const ok = legalRanks(st);
      as = opts.chooseJoker ? opts.chooseJoker(ok.slice()) : (ok.includes('10') ? '10' : ok[0]);
      if (!ok.includes(as)) as = ok[0];
    }
    const v = validateMove(st, pi, [card.id], as);
    if (v.ok) applyPlay(st, p, v, action);
    else {
      log(st, `${p.name} revealed ${describe(1, card.rank)} but could not play it.`);
      p.faceDown = p.faceDown.filter(c => c !== card);
      card.as = card.rank; st.pile.push(card);
      doPickup(st, p, null);
    }
  } else return err('Unknown action.');
  st.turns++;
  if (st.phase === 'play') {
    const active = st.players.filter(q => !q.finished).length;
    const sig = signature(st); st.seen[sig] = (st.seen[sig] || 0) + 1;
    if (st.seen[sig] >= 4) adjudicate(st, 'repeated position');
    else if (st.turns > MAX_TURNS) adjudicate(st, 'turn limit');
    else if (st.passCount >= active * 2) adjudicate(st, 'nobody can move');
  }
  return { ok: true, events: st.events };
}

/* ---------- information barrier: what player `pi` is allowed to know ---------- */
function publicView(st, pi) {
  const cl = c => ({ ...c });
  return {
    me: pi, current: st.current, direction: st.direction, phase: st.phase, opening: st.opening,
    effRank: st.effRank, restriction: st.restriction, handSize: st.handSize,
    pile: st.pile.map(cl), drawCount: st.drawPile.length, burnedCount: st.burned.length,
    finishOrder: st.finishOrder.slice(),
    players: st.players.map(p => ({
      index: p.index, name: p.name, finished: p.finished, place: p.place, controller: p.controller, personality: p.personality,
      handCount: p.hand.length, faceUp: p.faceUp.map(cl), faceDownCount: p.faceDown.length,
      hand: p.index === pi ? p.hand.map(cl) : undefined,
      faceDownIds: p.faceDown.map(c => c.id),   // ids only (needed to click a slot); never rank/suit
    })),
  };
}
function auditCards(st) {
  const all = [...st.drawPile, ...st.pile, ...st.burned];
  st.players.forEach(p => all.push(...p.hand, ...p.faceUp, ...p.faceDown));
  const ids = new Set(all.map(c => c.id));
  if (all.length !== st.total) throw new Error(`Card count ${all.length} != ${st.total}`);
  if (ids.size !== all.length) throw new Error('Duplicate card ids');
  st.players.forEach(p => { if (!st.adjudicated && p.finished && cardsLeft(p)) throw new Error('Finished player holds cards'); });
  return true;
}

const API = { RANKS, PLAIN, STR, WILD, FACE, LOW, SUITS, mulberry32, createDeck, shuffle, handSizeFor, autoJokers, newGame, chooseFaceUp, beginPlay,
  rankAllowed, legalRanks, validateMove, getLegalMoves, act, publicView, auditCards, nextEligible, wouldBurn, cardsLeft, zoneOf, fourOfKind, isOpenCard, describe };
if (typeof module !== 'undefined' && module.exports) module.exports = API; else root.CardEngine = API;
})(typeof window !== 'undefined' ? window : globalThis);
