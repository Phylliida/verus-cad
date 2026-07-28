/* app.js — UI wiring. Three modes sharing one editor:
 *   pts  — lambda cube: Church-style PTS checker + substitution stepper
 *   bckw — combinators: Turner compilation + principal type inference
 *   cek  — environment machine: closures and lookups, no substitution
 * Uses globals LambdaCore, Comb, Machine, EXAMPLES.
 */
(function () {
'use strict';
const L = LambdaCore, CB = Comb, MK = Machine;
const $ = id => document.getElementById(id);

let stepState = null; // pts/bckw: {kind, term, env, n} · cek: {kind:'cek', st}

// ---------- mode & cube axes ----------
const rules = () => ({ poly: $('tgl-poly').checked, typeops: $('tgl-typeops').checked, dep: $('tgl-dep').checked });

const SYSTEMS = [
  ['',    'λ→',  'simply typed lambda calculus'],
  ['P',   'λ2',  'System F — polymorphism'],
  ['T',   'λω̲',  'weak λω — type operators'],
  ['D',   'λP',  'dependent types'],
  ['PT',  'λω',  'System Fω — polymorphism + type operators'],
  ['PD',  'λP2', 'polymorphism + dependent types'],
  ['TD',  'λPω̲', 'dependent types + type operators'],
  ['PTD', 'λC',  'Calculus of Constructions — the whole cube'],
];

const MODE_INFO = {
  pts:  { btns: ['check', 'step', 'normalize'] },
  bckw: { btns: ['compile + infer', 'step', 'normalize'],
          sysname: 'BCKW', sysdesc: 'combinators — types inferred, Hilbert style' },
  cek:  { btns: ['start', 'step', 'run'],
          sysname: 'CEK', sysdesc: 'environment machine — closures, no substitution' },
};

function currentMode() {
  return document.querySelector('input[name="mode"]:checked').id.replace('mode-', '');
}

function updateSys() {
  if (currentMode() !== 'pts') return;
  const r = rules();
  const key = (r.poly ? 'P' : '') + (r.typeops ? 'T' : '') + (r.dep ? 'D' : '');
  const e = SYSTEMS.find(x => x[0] === key);
  $('sysname').textContent = e[1];
  $('sysdesc').textContent = e[2];
}

function updateMode() {
  const m = currentMode();
  stepState = null; $('stepinfo').textContent = '';
  $('check').textContent = MODE_INFO[m].btns[0];
  $('stepBtn').textContent = MODE_INFO[m].btns[1];
  $('norm').textContent = MODE_INFO[m].btns[2];
  $('axes-sec').classList.toggle('disabled', m !== 'pts');
  if (m === 'pts') updateSys();
  else { $('sysname').textContent = MODE_INFO[m].sysname; $('sysdesc').textContent = MODE_INFO[m].sysdesc; }
}

// ---------- output ----------
function showOut(text, cls) { const o = $('out'); o.textContent = text; o.className = cls || ''; }

function errText(e) {
  let s = e.message || String(e);
  if (e.line != null) {
    const lineText = ($('src').value.split('\n'))[e.line - 1] || '';
    s = `line ${e.line}, column ${e.col}: ${s}\n  ${lineText}\n  ${' '.repeat(Math.max(0, e.col - 1))}^`;
  }
  return s;
}

// ---------- check / compile / start ----------
function doCheck() {
  stepState = null; $('stepinfo').textContent = '';
  const m = currentMode();
  try {
    if (m === 'pts') {
      const r = L.checkProgram($('src').value, rules());
      let t = r.lines.join('\n');
      if (r.finalType) t += (t ? '\n' : '') + '─'.repeat(40) + '\n⊢ expression : ' + L.show(r.finalType);
      showOut(t || '(nothing to check)', 'ok');
    } else if (m === 'bckw') {
      const r = CB.compileProgram($('src').value);
      const lines = r.lines.map(d =>
        `${d.name} : ${CB.showType(d.type, r.sub)}\n${' '.repeat(d.name.length)} := ${L.show(d.compiled)}`);
      let t = lines.join('\n');
      if (r.finalCompiled) {
        t += (t ? '\n' : '') + '─'.repeat(40) +
          `\n⊢ expression : ${CB.showType(r.finalType, r.sub)}` +
          `\n  compiled: ${L.show(r.finalCompiled)}`;
      }
      t += `\n\nsize: ${r.lamSize} λ-nodes → ${r.combSize} combinator nodes (defs shared by name, not inlined)`;
      showOut(t, 'ok');
    } else {
      const st = MK.cekInit($('src').value);
      if (!st.control) { showOut('no final expression to evaluate — add one after the definitions.', 'err'); return; }
      stepState = { kind: 'cek', st };
      $('out').className = 'trace';
      $('out').textContent = MK.cekShow(st) + '\n';
      $('stepinfo').textContent = 'machine started — hit step';
    }
  } catch (e) {
    if (m === 'pts' && e.code === 'untyped') {
      showOut(errText(e) + '\n\n→ untyped mode: "step" and "normalize" still work.', 'info');
    } else {
      showOut(errText(e), 'err');
    }
  }
}

// ---------- step ----------
function doStep() {
  const m = currentMode();
  try {
    if (m === 'cek') {
      if (!stepState || stepState.kind !== 'cek') {
        const st = MK.cekInit($('src').value);
        if (!st.control) { showOut('no final expression to evaluate — add one after the definitions.', 'err'); return; }
        stepState = { kind: 'cek', st };
        $('out').className = 'trace';
        $('out').textContent = MK.cekShow(st) + '\n';
        return;
      }
      const st = MK.cekStep(stepState.st);
      stepState.st = st;
      const o = $('out');
      o.textContent += '\n' + MK.cekShow(st) + '\n';
      o.scrollTop = o.scrollHeight;
      if (st.done || st.stuck) { stepState = null; $('stepinfo').textContent = ''; }
      return;
    }

    // pts & bckw share the trace UI; they differ in parser + step function
    if (!stepState) {
      const src = $('src').value;
      if (m === 'pts') {
        const p = L.evalProgram(src);
        if (!p.final) { showOut('no final expression to evaluate — add one after the definitions.', 'err'); return; }
        stepState = { kind: 'pts', term: p.final, env: p.env, n: 0 };
      } else {
        const r = CB.compileProgram(src);
        if (!r.finalCompiled) { showOut('no final expression to evaluate — add one after the definitions.', 'err'); return; }
        stepState = { kind: 'bckw', term: r.finalCompiled, env: r.env, n: 0 };
      }
      $('out').className = 'trace';
      $('out').textContent = '0: ' + L.show(stepState.term) + '\n';
      $('stepinfo').textContent = 'stepping… (edit the source to reset)';
      return;
    }
    const stepFn = stepState.kind === 'bckw' ? CB.stepComb : L.step;
    const s = stepFn(stepState.term, stepState.env);
    if (s === null) {
      $('out').textContent += '— normal form reached —';
      stepState = null; $('stepinfo').textContent = '';
      return;
    }
    stepState.term = s; stepState.n++;
    const o = $('out');
    o.textContent += stepState.n + ': ' + L.show(s) + '\n';
    o.scrollTop = o.scrollHeight;
  } catch (e) {
    showOut(errText(e), 'err');
    stepState = null; $('stepinfo').textContent = '';
  }
}

// ---------- normalize / run ----------
function doNormalize() {
  stepState = null; $('stepinfo').textContent = '';
  const m = currentMode();
  try {
    if (m === 'cek') {
      const st = MK.cekRun(MK.cekInit($('src').value), 1000);
      if (!st.control) { showOut('no final expression to evaluate — add one after the definitions.', 'err'); return; }
      showOut(MK.cekShow(st) + (st.done || st.stuck ? '' : `\n(step cap of 1000 reached)`), st.done ? 'ok' : 'info');
      return;
    }
    if (m === 'pts') {
      const p = L.evalProgram($('src').value);
      if (!p.final) { showOut('no final expression to evaluate — add one after the definitions.', 'err'); return; }
      const r = L.normalize(p.final, p.env, 1000);
      showOut((r.capped ? `did not terminate within ${r.steps} steps; current term:\n` : `normal form (${r.steps} steps):\n`) + L.show(r.term),
        r.capped ? 'info' : 'ok');
    } else {
      const r = CB.compileProgram($('src').value);
      if (!r.finalCompiled) { showOut('no final expression to evaluate — add one after the definitions.', 'err'); return; }
      const n = CB.normalizeComb(r.finalCompiled, r.env, 1000);
      showOut((n.capped ? `did not terminate within ${n.steps} steps; current term:\n` : `normal form (${n.steps} steps):\n`) + L.show(n.term),
        n.capped ? 'info' : 'ok');
    }
  } catch (e) {
    showOut(errText(e), 'err');
  }
}

// ---------- examples ----------
function loadExample(ex) {
  $('src').value = ex.src;
  $('mode-' + (ex.mode || 'pts')).checked = true;
  if (ex.mode === 'pts' || !ex.mode) {
    $('tgl-poly').checked = !!ex.poly;
    $('tgl-typeops').checked = !!ex.typeops;
    $('tgl-dep').checked = !!ex.dep;
  }
  updateMode();
  doCheck();
}

function init() {
  for (const ex of EXAMPLES) {
    const b = document.createElement('button');
    b.textContent = ex.name;
    b.onclick = () => loadExample(ex);
    $('examples').appendChild(b);
  }
  for (const id of ['tgl-poly', 'tgl-typeops', 'tgl-dep']) $(id).addEventListener('change', updateSys);
  for (const id of ['mode-pts', 'mode-bckw', 'mode-cek']) $(id).addEventListener('change', updateMode);
  $('check').addEventListener('click', doCheck);
  $('stepBtn').addEventListener('click', doStep);
  $('norm').addEventListener('click', doNormalize);
  $('src').addEventListener('input', () => { stepState = null; $('stepinfo').textContent = ''; });
  updateMode();
  loadExample(EXAMPLES[0]);
}

init();
})();
