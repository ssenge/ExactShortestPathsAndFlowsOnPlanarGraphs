# Checks of notes/DIAMETER.md

Run on 3 Nov 2026 on region bags built by the engine of `sim/s9`, on the families dl, grid, k2m, fan, nested, pend and flower. No check failed in any lane below. Timed lanes do not reproduce exact counts.

## Main lanes, `diam.py`

| | Normal lane | Big lane |
|---|---|---|
| Runs | 14,540 | 4,773 |
| Bags with a separator | 350,968 | 197,459 |
| Eccentricities, E(u) against BFS | 1,457,083 | 764,177 |
| Token evaluations, each equal to d_G | 47,342,058 | 77,819,749 |
| Sandwich and near hub | 5,310,842 | 3,129,237 |
| Lemma 2, patterns per face | 537,479 | 324,488 |
| Lemma 3, nodes of the segment tree | 28,150,329 | 31,091,661 |
| Alternation, sampled pairs | 5,250,602 | 3,021,357 |
| Step 3, first-hit formula, vertices | 872,783 | 421,801 |
| Step 2, recursive table, entries | 68,569,213 | 50,117,322 |
| Corners of a component on one face, Euler | 350,968 | 197,459 |
| Largest n, D | 550, 36 | 550, 38 |
| Largest number of bags | 443 | 438 |
| Largest \|E(P_X)\| / D | 11.0 | 10.75 |
| Largest tokens / (2\|E(P_X)\|)² | 31% | 31% |
| Largest dictionary / (2\|E(P_X)\|)² | 130% | 124% |
| Largest patterns / K², for K ≥ 8 | 25% | 22% |

## Growth on full grids, `diam.py scale`

| k | n | D | \|E(P_X)\| / D | tokens / (2\|E\|)² | dictionary / (2\|E\|)² |
|---|---|---|---|---|---|
| 6 | 36 | 10 | 2.87 | 8% | 64% |
| 10 | 100 | 18 | 3.07 | 5% | 54% |
| 14 | 196 | 26 | 3.78 | 4% | 40% |
| 18 | 324 | 34 | 4.42 | 5% | 39% |
| 24 | 576 | 46 | 5.09 | 7% | 51% |
| 30 | 900 | 58 | 5.48 | 6% | 42% |
| 40 | 1600 | 78 | 6.19 | 8% | 52% |

Every ratio is flat or grows slowly, which fits Õ(D²) words. This is not a measurement of rounds.

## Negative controls, `diam.py ctl`, 250 s per mutation

| Mutation | Runs | Runs with a wrong value | Too high | Too low |
|---|---|---|---|---|
| Top token on the own face, whatever its child | 2,254 | 906 | 25,599 | 0 |
| Own face: only the top token, dropped if in the own child | 2,439 | 0 | 0 | 0 |
| Offset of a token replaced by 0 | 2,388 | 1,639 | 0 | 94,246 |
| P_X without ancestors and without T-paths | 2,327 | 1,533 | 48,327 | 0 |

The second mutation did not fire on these families, so these lanes do not show that the second token is needed, though it fired on the adversary's instances (2 of 150 and 1 of 71). Two tokens occur (1,304 patterns in 628 runs), and the second is often a farthest vertex (1,013 of 22,390 cases), but it was never the only one. Perturbing such instances and rebuilding the bags did not fire it either. `diam.py second` forces the configuration: the root separator ends at a cut vertex a, and its closing edge separates two combs at a, in one corner of P. There the mutation gives wrong values for 18 of 48, 35 of 77 and 70 of 158 vertices, and the unmutated rule for none.

## Sum Corollary, `diam.py sum`, 60 s

250 runs and 25,226 values S(u) from the tables of the corollary, all equal to the sum over BFS. Each mutation made some S(u) wrong: without the subtraction for the own child in 250 runs, without the sum of offsets in 250, with count 1 per pattern in 247, and with hubs outside X° in 249.

## Limits

- Rounds, messages and who knows what: no CONGEST simulation. Word counts are counted only for tokens and dictionary entries.
- The engine leaves a bag as a leaf if it finds no separator in its tries, so leaf size is not bounded as in (H1), and the forced root is the only hand-made case.
- Below 40 × 40 grids only, and random lanes stop at n = 550.
- The weighted form of the Sum Corollary is not run.
- `diam.py` checks Lemma 1 only on token pairs, reads true distances in E(u) and not the output of Steps 2 and 3, checks Lemma 3 on the nodes of the segment tree and alternation on 40 sampled pairs per face, and has no negative control for Lemmas 2 and 3. About a third of the vertices lie in forced leaves, which are trivially right, and wheels never split here. The adversary's own code, see `notes/DIAMETER.md`, Section 6, closes these on its instances and is not in this repository.

## Reproduce

    python3 -I sim/diameter/diam.py 3001 1500; python3 -I sim/diameter/diam.py 3002 1500 big
    python3 -I sim/diameter/diam.py ctl 3099 250; python3 -I sim/diameter/diam.py scale
    python3 -I sim/diameter/diam.py second; python3 -I sim/diameter/diam.py sum 4001 60

Needs numpy, scipy and networkx.
