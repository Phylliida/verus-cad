// Forkless-part enumerator for rank-5 quivers (positive-campaign, Probe 18 follow-up).
// For each of the 5 slow-decliner quivers: BFS the mutation class up to an entry cap,
// count distinct FORKLESS quivers (Warkentin, up to relabeling+sign) with max-entry <= t
// as t grows. Plateau => finite forkless part (decidable); unbounded growth => the
// non-recognizable substrate.
use std::collections::{HashSet, VecDeque};
use std::io::Write;

const PAIRS: [(usize, usize); 10] =
    [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)];
type Q = [i64; 10];

#[inline]
fn pidx(i: usize, j: usize) -> usize {
    match (i, j) {
        (0,1)=>0,(0,2)=>1,(0,3)=>2,(0,4)=>3,(1,2)=>4,
        (1,3)=>5,(1,4)=>6,(2,3)=>7,(2,4)=>8,(3,4)=>9,_=>unreachable!()
    }
}
#[inline]
fn bval(q: &Q, i: usize, j: usize) -> i64 {
    if i == j { 0 } else if i < j { q[pidx(i,j)] } else { -q[pidx(j,i)] }
}
fn mutate(q: &Q, k: usize) -> Q {
    let mut r = [0i64; 10];
    for (p, &(i, j)) in PAIRS.iter().enumerate() {
        r[p] = if i == k || j == k { -q[p] }
        else {
            let a = bval(q, i, k); let b = bval(q, k, j);
            q[p] + (a.abs() * b + a * b.abs()) / 2
        };
    }
    r
}
#[inline]
fn maxent(q: &Q) -> i64 { q.iter().map(|x| x.abs()).max().unwrap() }

fn full(q: &Q) -> [[i64; 5]; 5] {
    let mut m = [[0i64; 5]; 5];
    for &(i, j) in PAIRS.iter() { let v = q[pidx(i,j)]; m[i][j] = v; m[j][i] = -v; }
    m
}
fn acyclic_sub(m: &[[i64; 5]; 5], verts: &[usize]) -> bool {
    fn dfs(u: usize, m: &[[i64;5];5], verts: &[usize], color: &mut [u8;5]) -> bool {
        color[u] = 1;
        for &w in verts {
            if w != u && m[u][w] > 0 {
                if color[w] == 1 { return false; }
                if color[w] == 0 && !dfs(w, m, verts, color) { return false; }
            }
        }
        color[u] = 2; true
    }
    let mut color = [0u8; 5];
    for &v in verts { if color[v] == 0 && !dfs(v, m, verts, &mut color) { return false; } }
    true
}
fn is_fork(q: &Q) -> bool {
    if q.iter().any(|x| x.abs() < 2) { return false; }     // abundant
    let m = full(q);
    let all = [0usize,1,2,3,4];
    if acyclic_sub(&m, &all) { return false; }             // non-acyclic
    for r in 0..5 {
        let qp: Vec<usize> = (0..5).filter(|&i| i != r && m[r][i] > 0).collect();
        let qm: Vec<usize> = (0..5).filter(|&j| j != r && m[j][r] > 0).collect();
        if qp.len() + qm.len() != 4 { continue; }
        if !acyclic_sub(&m, &qp) || !acyclic_sub(&m, &qm) { continue; }
        let mut ok = true;
        'o: for &i in &qp { for &j in &qm {
            if !(m[i][j] > m[r][i] && m[i][j] > m[j][r]) { ok = false; break 'o; }
        }}
        if ok { return true; }
    }
    false
}
fn perms5() -> Vec<[usize; 5]> {
    let mut out = Vec::new();
    fn rec(k: usize, a: &mut [usize; 5], out: &mut Vec<[usize; 5]>) {
        if k == 5 { out.push(*a); return; }
        for i in k..5 { a.swap(k, i); rec(k + 1, a, out); a.swap(k, i); }
    }
    rec(0, &mut [0,1,2,3,4], &mut out);
    out
}
fn canon(q: &Q, perms: &[[usize; 5]]) -> Q {
    let m = full(q);
    let mut best: Option<Q> = None;
    for pi in perms {
        let mut r = [0i64; 10];
        for (p, &(i, j)) in PAIRS.iter().enumerate() { r[p] = m[pi[i]][pi[j]]; }
        if best.map_or(true, |b| r < b) { best = Some(r); }
        let mut rn = r; for x in rn.iter_mut() { *x = -*x; }
        if rn < best.unwrap() { best = Some(rn); }
    }
    best.unwrap()
}

#[inline]
fn sqsum(q: &Q) -> i64 { q.iter().map(|x| x * x).sum() }
// a "local min of Sum b^2": no single mutation strictly decreases Sum b^2
fn is_local_min(q: &Q) -> bool {
    let s = sqsum(q);
    for k in 0..5 { if sqsum(&mutate(q, k)) < s { return false; } }
    true
}

fn run(name: &str, seed: Q, maxcap: i64, statecap: usize, perms: &[[usize; 5]], ths: &[i64]) {
    let mut seen: HashSet<Q> = HashSet::new();
    let mut forkless: HashSet<Q> = HashSet::new();
    let mut localmins: HashSet<Q> = HashSet::new();   // canonical Sum-b^2 local minima
    let mut gmin: i64 = i64::MAX;
    let mut gmin_stratum: HashSet<Q> = HashSet::new(); // canonical global-min stratum
    let mut queue: VecDeque<Q> = VecDeque::new();
    let mut visit = |u: &Q, forkless: &mut HashSet<Q>, localmins: &mut HashSet<Q>,
                     gmin: &mut i64, strat: &mut HashSet<Q>| {
        if !is_fork(u) { forkless.insert(canon(u, perms)); }
        if is_local_min(u) { localmins.insert(canon(u, perms)); }
        let s = sqsum(u);
        if s < *gmin { *gmin = s; strat.clear(); strat.insert(canon(u, perms)); }
        else if s == *gmin { strat.insert(canon(u, perms)); }
    };
    seen.insert(seed); queue.push_back(seed);
    visit(&seed, &mut forkless, &mut localmins, &mut gmin, &mut gmin_stratum);
    let mut cut = false;
    while let Some(cur) = queue.pop_front() {
        for k in 0..5 {
            let u = mutate(&cur, k);
            if maxent(&u) > maxcap { continue; }
            if seen.contains(&u) { continue; }
            if seen.len() >= statecap { cut = true; break; }
            seen.insert(u);
            visit(&u, &mut forkless, &mut localmins, &mut gmin, &mut gmin_stratum);
            queue.push_back(u);
        }
        if cut { break; }
    }
    // breakdown of forkless: non-abundant vs abundant (abundant non-forks would be the surprising ones)
    let n_abund = forkless.iter().filter(|q| q.iter().all(|x| x.abs() >= 2)).count();
    let n_abund_noncyc = forkless.iter()
        .filter(|q| q.iter().all(|x| x.abs() >= 2) && !acyclic_sub(&full(q), &[0,1,2,3,4])).count();
    print!("{}: comp={} forkless={} (abundant={} abund&noncyc={}) localmins={} gmin={} gmin_stratum={} cut={} | forkless(t): ",
           name, seen.len(), forkless.len(), n_abund, n_abund_noncyc, localmins.len(), gmin, gmin_stratum.len(), cut);
    for &t in ths {
        let c = forkless.iter().filter(|c| maxent(c) <= t).count();
        print!("t{}={} ", t, c);
    }
    // local-min count by max-entry threshold (finite => min-core decidable; growing => false floors)
    print!("| localmins(t): ");
    for &t in ths { print!("t{}={} ", t, localmins.iter().filter(|c| maxent(c) <= t).count()); }
    println!();
    // dump local minima sorted by max-entry (look for a growing family = hairpin among minima)
    if std::env::args().any(|a| a == "dump") {
        let mut lm: Vec<Q> = localmins.iter().cloned().collect();
        lm.sort_by_key(|q| maxent(q));
        for q in &lm { println!("    localmin maxent={:>4} sq={:>7} {:?}", maxent(q), sqsum(q), q); }
    }
}

fn is_abundant(q: &Q) -> bool { q.iter().all(|x| x.abs() >= 2) }
fn is_vortex_free(q: &Q) -> bool {
    let m = full(q);
    for quad in [[0,1,2,3],[0,1,2,4],[0,1,3,4],[0,2,3,4],[1,2,3,4]] {
        for &apex in &quad {
            let o: Vec<usize> = quad.iter().cloned().filter(|&v| v != apex).collect();
            if o.iter().any(|&w| m[apex][w] == 0) { continue; }
            let allout = o.iter().all(|&w| m[apex][w] > 0);
            let allin  = o.iter().all(|&w| m[apex][w] < 0);
            if !(allout || allin) { continue; }
            let (a,b,c) = (o[0],o[1],o[2]);
            let cyc = (m[a][b]>0 && m[b][c]>0 && m[c][a]>0) || (m[a][c]>0 && m[c][b]>0 && m[b][a]>0);
            if cyc { return false; }
        }
    }
    true
}
// returns Some(component_size) if no non-abundant quiver is reachable within cap (mutation-abundant
// up to that cap); None if a weight<2 is found.
fn mut_abundant_upto(seed: &Q, cap: i64, statecap: usize) -> Option<usize> {
    let mut seen: HashSet<Q> = HashSet::new(); seen.insert(*seed);
    let mut q: VecDeque<Q> = VecDeque::new(); q.push_back(*seed);
    while let Some(cur) = q.pop_front() {
        for k in 0..5 {
            let u = mutate(&cur, k);
            if maxent(&u) > cap { continue; }
            if !is_abundant(&u) { return None; }
            if seen.contains(&u) { continue; }
            if seen.len() >= statecap { return Some(seen.len()); }
            seen.insert(u); q.push_back(u);
        }
    }
    Some(seen.len())
}
// forkless count (up to iso) with maxent<=t, from a BFS to cap
fn forkless_counts(seed: &Q, cap: i64, statecap: usize, perms: &[[usize;5]], ths: &[i64]) -> (Vec<usize>, bool) {
    let mut seen: HashSet<Q> = HashSet::new(); seen.insert(*seed);
    let mut fl: HashSet<Q> = HashSet::new();
    let mut q: VecDeque<Q> = VecDeque::new(); q.push_back(*seed);
    if !is_fork(seed) { fl.insert(canon(seed, perms)); }
    let mut cut = false;
    while let Some(cur) = q.pop_front() {
        for k in 0..5 {
            let u = mutate(&cur, k);
            if maxent(&u) > cap || seen.contains(&u) { continue; }
            if seen.len() >= statecap { cut = true; break; }
            seen.insert(u);
            if !is_fork(&u) { fl.insert(canon(&u, perms)); }
            q.push_back(u);
        }
        if cut { break; }
    }
    (ths.iter().map(|&t| fl.iter().filter(|c| maxent(c) <= t).count()).collect(), cut)
}

fn search_mode(perms: &[[usize;5]]) {
    // Phase 1: collect DISTINCT mutation-abundant vortex-free classes (canonical), from
    // all 1024 weight-2 orientations of K5 + random weight-{2,3} seeds.
    let mut ma_vf: HashSet<Q> = HashSet::new();
    let mut n_seeds = 0; let mut n_ma = 0;
    let mut consider = |s: Q, ma_vf: &mut HashSet<Q>, n_ma: &mut usize| {
        if !is_abundant(&s) { return; }
        if mut_abundant_upto(&s, 24, 80_000).is_none() { return; }   // not mutation-abundant
        *n_ma += 1;
        if is_vortex_free(&s) { ma_vf.insert(canon(&s, perms)); }
    };
    for bits in 0u32..1024 {
        let mut s = [0i64; 10];
        for p in 0..10 { s[p] = if (bits >> p) & 1 == 1 { 2 } else { -2 }; }
        consider(s, &mut ma_vf, &mut n_ma); n_seeds += 1;
    }
    let mut st: u64 = 0x243F6A8885A308D3;
    let mut rng = || { st ^= st << 13; st ^= st >> 7; st ^= st << 17; st };
    for _ in 0..200_000 {
        let mut s = [0i64; 10];
        for p in 0..10 { s[p] = [-3,-2,2,3][(rng() % 4) as usize]; }
        consider(s, &mut ma_vf, &mut n_ma); n_seeds += 1;
    }
    println!("phase1: {} seeds, {} mutation-abundant, {} DISTINCT mutation-abundant vortex-free classes",
             n_seeds, n_ma, ma_vf.len());
    let _ = std::io::stdout().flush();

    // Phase 2: measure each distinct class's forkless part at HIGH cap; thresholds BELOW cap so
    // "still rising at t=160 (cap 240)" => candidate INFINITE; "plateau well below cap" => FINITE.
    let ths = [40, 70, 100, 130, 160i64];
    let cap = 240i64;
    let cands: Vec<Q> = ma_vf.into_iter().collect();
    let mut rising = 0; let mut finite = 0; let mut hits: Vec<(Q, Vec<usize>)> = Vec::new();
    for (i, s) in cands.iter().enumerate() {
        let (counts, cut) = forkless_counts(s, cap, 2_000_000, perms, &ths);
        let n = counts.len();
        // plateau => the last two thresholds (both < cap) are equal AND the count is bounded
        let still_rising = counts[n-1] > counts[n-2];
        if still_rising { rising += 1; hits.push((*s, counts.clone())); }
        else { finite += 1; }
        if i < 30 || still_rising {
            println!("  class {:?}  forkless(t={:?})={:?}  -> {}{}",
                     s, ths, counts, if still_rising {"RISING (candidate infinite)"} else {"plateau (finite)"},
                     if cut {" [cut]"} else {""});
            let _ = std::io::stdout().flush();
        }
    }
    println!("\nsummary: {} distinct MA vortex-free classes: {} plateau (finite forkless), {} still-rising@cap {} (candidate infinite)",
             cands.len(), finite, rising, cap);
    if !hits.is_empty() {
        println!("  candidate-infinite classes (verify at higher cap!):");
        for (s, c) in hits.iter().take(10) { println!("    {:?} counts={:?}", s, c); }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.iter().any(|a| a == "search") {
        let perms = perms5();
        search_mode(&perms);
        return;
    }
    let maxcap: i64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(80);
    let statecap: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(30_000_000);
    // i64 product bound: intermediate |b_ik|*b_kj <= maxcap^2 must fit in i64.
    assert!(maxcap < 3_000_000_000, "maxcap too large for i64 (products would overflow) — use i128/bigint");
    let perms = perms5();
    let ths: Vec<i64> = [20,30,40,50,60,80,100,120,160,200]
        .into_iter().filter(|&t| t <= maxcap).collect();
    let quivers: [(&str, Q); 7] = [
        // CALIBRATION references first:
        ("acyclic5(finite?)", [2,2,2,2,2,2,2,2,2,2]),   // mutation-acyclic; expect PLATEAU
        ("fomin_n5k1",        [2,-6,-6,2,10,10,2,2,2,2]),// proper=False; unknown
        // the 5 slow-decliners:
        ("#9",  [0,-1,0,2,-1,3,-3,2,2,3]),
        ("#13", [2,-2,-1,2,-1,0,-2,2,0,-2]),
        ("#14", [-2,-2,2,-2,-2,-2,1,2,1,2]),
        ("#15", [2,-2,2,-2,2,1,-1,2,2,-2]),
        ("#19", [-2,0,0,-2,-2,-1,2,2,1,-2]),
    ];
    println!("maxcap={} statecap={} | forkless(maxent<=t) — plateau=finite, growth=infinite", maxcap, statecap);
    for (name, seed) in quivers.iter() {
        run(name, *seed, maxcap, statecap, &perms, &ths);
    }
}
