# Checks of notes/MAXFLOW.md

Run on 2 Nov 2026 with K = 9, ε = 1/12. No check failed in any lane below. Timed lanes do not reproduce exact counts.

## Sections 2 and 3, `mf.py`

Portal distances are perturbed within [d, (1+ε)d] by noise, and the result is compared with an independent Dinic.

| | Normal lane | Big lane |
|---|---|---|
| Instances | 274,330 | 85,147 |
| Iterations of the Step Lemma | 1,661,935 | 571,057 |
| Portal bounds (B), both sides | 47,232,304 | 37,161,995 |
| J bounds, J ≤ Kλ | 1,661,935 | 571,057 |
| Filling keeps portals | 7,504,640 | 3,658,417 |
| Residual nonnegative | 129,859,422 | 90,077,090 |
| Reduced costs nonnegative | 19,450,962 | 11,940,138 |
| Value, feasibility, conservation, antisymmetry, gap | 274,330 each | 85,147 each |
| Largest λ | 6,072,908 | 5,267,122 |
| Largest R, portals | 27, 17 | 44, 28 |
| Instances with p > 0 at the end | 73,907 | 23,030 |

Capacity classes: directed, one way, unit, huge and with zeros about equally often, symmetric twice as often.

**Negative controls.** All fired.

| Mutation | Runs | Failures |
|---|---|---|
| No division in the portal bounds | 137,760 | B_upper 5,562,605; fill 95,000; J ≤ Kλ 60,905; residual 61,010 |
| One source in place of all portals | 190,481 | fill 492,533; residual 110,988 |
| Reduced costs without the term p | 52,877, of which 19,119 with p > 0 | reduced_nonneg 19,119 |
| Too few iterations | 293,261, of which 134,395 with p > 0 | gap 114,339; value 10,672 |

## Sections 4 and 5, `forced.py`

| | Networks N (`net`) | General roots (`gen`) |
|---|---|---|
| Instances | 2,987 | 6,137 (2,841 face, 3,296 fundamental cycle) |
| Forced roots | 2,942 | 6,137 |
| Lemma V in region form | 314,937 | 534,753 |
| Root pairs with the glued metric | 1,786,552 | 450,532 |
| Lemma 16 entries | 128,112,154 | 116,730,252 |
| R1 pairs | 9,945,983 | 8,322,776 |
| End-to-end gluings | 585,644 | 736,336 |
| Hub checks | 1,096,303 | 1,314,900 |
| Tiles | 1,232,343 | 1,450,652 |
| Lemmas B2, B3, B4 | 163,519 | 291,866 |

On N: planarity, facial cycle, designed rotation and portals on the cycle hold on all 3,003 networks built; the metric of Lemma N matched Γ in 1,079,210 checks; the largest hop ratio
was exactly 6, against the bound 6D + 2. Largest depth 22, largest a_Y 4.

**Negative control.** With the wrong glued metric at the root: 314 failures in 9,954 root pairs, 767 runs.

## Limits

- `mf.py` works on Γ with scale 2(faces+1), so Lemma N(6) is not exercised there. Noise means four fixed modes.
- `mf.py` runs simple networks only and takes the number of iterations from nU, which suffices there. The failure on parallel arcs of one direction, `notes/MAXFLOW.md`, Section 3, is not run here.
- `forced.py` does not check the diameter of T_X, c(X) or region connectivity. Below the root it uses fundamental cycles, and bags with no cycle in the tries stay leaves.
- The hop bound was tested as 6D + 8 in the lanes above. It is now 6D + 2 in the code; the measured ratio stays at most 6.
- Portal containment on the cycle is at face level.
- The tolerance in `forced.py` is relative, since lengths reach 1e10.
- Neither script combines N, δ, the Step Lemma and SSSP on N.

## Not covered

- Rounds, messages and who knows what: no CONGEST simulation.
- The black boxes (G3), (G5), (G6) and the given embedding.
- Emulators here are perturbed pieces and wheels, not the emulators of a real execution of [1, Lemma 15].
- Sizes above a few hundred vertices.

## Reproduce

    python3 -I sim/maxflow/mf.py 2001 1500; python3 -I sim/maxflow/mf.py 2002 1500 big; python3 -I sim/maxflow/mf.py ctl 2099 300
    python3 -I sim/maxflow/forced.py 2003 1500 net; python3 -I sim/maxflow/forced.py 2004 1500 gen; python3 -I sim/maxflow/forced.py neg 2005 200

Needs numpy, scipy and networkx.
