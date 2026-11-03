# Checks of notes/APPROX_DIAMETER.md

Run on 3 Nov 2026 on region bags built by the engine of `sim/s9`, on the families of `sim/diameter/approx.py`. No check failed in any lane below. Timed lanes do not reproduce exact counts on another machine.

## Main lanes, `approx.py`

| | Normal lane | Big lane |
|---|---|---|
| Runs | 13,900 | 5,534 |
| Eccentricities, against BFS | 1,395,759 | 889,531 |
| Token evaluations | 28,286,778 | 56,339,774 |
| Invariant, per vertex and net point | 31,115,497 | 38,308,205 |
| Lemma 3, single crossing | 9,775,885 | 5,991,176 |
| Lemma 4, Sauer-Shelah count per face | 359,430 | 245,876 |
| Largest n | 526 | 526 |
| Largest rounded patterns per face | 142 | 265 |
| Largest tokens per bag | 142 | 265 |
| Largest portals per bag | 60 | 110 |
| Largest overestimate of E, in units of ρ | 3.00 | 4.00 |
| Largest underestimate of E, in units of ρ | 1.66 | 1.75 |

## Negative controls, `approx.py ctl`

The same seed and 150 seconds per mode. A control has fired if a count other than `under_rho` is positive.

| Control | Runs | What fired |
|---|---|---|
| `nochild` | 1,570 | over_3rho 620, FAIL.token_high 206,981 |
| `top1` | 1,683 | nothing in this lane, see below |
| `bottom` | 1,590 | low 913 |
| `norow` | 1,649 | high 13,275, over_3rho 13,849, FAIL.invariant_high 91,071, FAIL.token_high 14,500 |
| `netwide` | 1,501 | low 250, over_3rho 25, FAIL.token_low 44,819, FAIL.invariant_high 801, FAIL.token_high 553 |
| `noise` | 1,301 | over_3rho 3, FAIL.single_crossing 232,470, FAIL.levels 148, FAIL.token_high 228 |

`approx.py second` builds an instance that needs the second token. With only one token per pattern the eccentricity comes out too low, with both it never does. Runs that came out too low with one token: n = 77, ρ = 1: 28, n = 77, ρ = 2: 0, n = 158, ρ = 1: 69, n = 158, ρ = 2: 59, n = 48, ρ = 1: 0, n = 48, ρ = 2: 0, n = 256, ρ = 1: 102, n = 256, ρ = 2: 101.

## Scale, `approx.py scale`

Tokens against ρ on grids. E/ρ is the number of rounding levels.

| k | n | ρ | Net | Portals | Tokens | Dictionary | E/ρ |
|---|---|---|---|---|---|---|---|
| 20 | 400 | 1 | 38 | 78 | 260 | 9,392 | 248 |
| 20 | 400 | 2 | 25 | 52 | 247 | 5,951 | 124 |
| 20 | 400 | 4 | 16 | 33 | 215 | 2,547 | 62 |
| 20 | 400 | 8 | 10 | 19 | 108 | 869 | 31 |
| 20 | 400 | 16 | 6 | 10 | 45 | 243 | 15 |
| 30 | 900 | 1 | 45 | 86 | 544 | 14,745 | 450 |
| 30 | 900 | 2 | 27 | 58 | 515 | 9,322 | 225 |
| 30 | 900 | 4 | 17 | 35 | 416 | 3,951 | 112 |
| 30 | 900 | 8 | 11 | 21 | 242 | 1,147 | 56 |
| 30 | 900 | 16 | 6 | 13 | 58 | 308 | 28 |
| 40 | 1,600 | 1 | 95 | 195 | 1001 | 45,769 | 706 |
| 40 | 1,600 | 2 | 63 | 130 | 992 | 29,705 | 353 |
| 40 | 1,600 | 4 | 38 | 79 | 876 | 13,380 | 176 |
| 40 | 1,600 | 8 | 23 | 45 | 489 | 4,648 | 88 |
| 40 | 1,600 | 16 | 11 | 26 | 218 | 1,437 | 44 |

## Rounded patterns on grids, `grid_patterns.py`

This is the series quoted in Section 6 of the note: the number of rounded patterns on the k × k grid with P the boundary cycle and Φ its inner face, about 0.014·m⁴ with m²/K held near 0.4. It prints one line per k and needs `numpy` and `scipy`. The largest sizes take long. Smoke test on this code: 65 patterns at k = 26, 169 at k = 53, 248 at k = 100; the larger values in the note came from the same functions in a separate copy.

## Limits

- No CONGEST simulation. Rounds are not measured; words per bag are counted.
- ρ is a free parameter of the lanes. The lanes do not choose it as the theorem does.
- `FAIL.sauer` and `FAIL.interval` never fire, not even under noise, so they guard little. `FAIL.high` is nearly vacuous: (3 + 2H)ρ is at least the eccentricity on 14,032 of 14,048 sampled vertices, and `FAIL.low` is vacuous on about 65% of them. The sharper checks are the per-token bounds, `FAIL.token_low` and `FAIL.token_high`.
- The leaf cases of the note are hardly exercised with the small leaves of the lanes; with a leaf size of 60 they fire.
- The direction of rounding is not tested: rounding up instead of down also passes.
- Forced roots outside `second`, splits at z and trees T_X that are not BFS trees are never run.
- Forced leaves are not counted: about 19% of leaves exceed the stated leaf size.
- `scale` stops at k = 40, and the bound in the pair form of the theorem is not checked.
- The control `nochild` stays alive only through `FAIL.token_high`, and `top1` fires only on `second`.

## Reproduce

```
python3 -I sim/diameter/approx.py 5001 1200
python3 -I sim/diameter/approx.py 5002 1200 big
python3 -I sim/diameter/approx.py ctl 5099 150
python3 -I sim/diameter/approx.py scale
python3 -I sim/diameter/approx.py second
python3 -I sim/diameter/grid_patterns.py
```
