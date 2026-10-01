module

public import StructuralSieve.Defs
public import StructuralSieve.LPF
public import StructuralSieve.ZeroForce
public import StructuralSieve.Weight
public import StructuralSieve.GPS_StateMachine
public import StructuralSieve.Main
public import StructuralSieve.Truncated
public import StructuralSieve.SelfContained
public import StructuralSieve.Threshold
public import StructuralSieve.BinomialBound
public import StructuralSieve.BinomialCertificate
public import StructuralSieve.Rings
public import StructuralSieve.Newton
public import StructuralSieve.Certificate
public import StructuralSieve.Erdos
/-!
# StructuralSieve — Structural Reduction of Bertrand's Postulate

Formalization in Lean 4 / Mathlib4.
Author: Artur Flamandzki

Based on: "A Structural Reduction of Bertrand's Postulate"

## Status

**Fully verified — zero `sorry`.** The whole chain from Definition 2.1 to
`bertrand_chebyshev` is machine-checked. Mathlib's Bertrand
(`Nat.bertrand`/`exists_prime_lt_and_le_two_mul`) is **never used**, and
`Mathlib.NumberTheory.Bertrand` is imported nowhere on `Main`'s path: the atom
is closed by the self-contained `binomial_contradiction`. (`Erdos.lean` below
is the one file in the repository that does import it — an off-path reference
@[expose]
public instance, not reachable from `Main`; see *Extended development* below.)

## Two scopes: the Palomar excerpt and the full development

This repository serves two purposes, and they are deliberately different in
size. The **Palomar bounty excerpt** (`Challenge.lean`/`Solution.lean`/
`comparator.json`) is a narrow, three-theorem slice —
`prime_iff_uncovered_by_prev`, `prime_iff_uncovered_by_prev_general`,
`bertrand_chebyshev` — chosen to be the minimal self-contained closure an
automated reviewer can check statement-by-statement; it never imports
`Rings.lean`, `Newton.lean`, `Certificate.lean`, or `Erdos.lean`, with or
without those files present in the repository. The **full development**
described below is everything this project has actually proved, including
results that are not part of that narrow excerpt because they are separate,
self-standing facts (not because they are less true or less verified). See
*Extended development* at the end of this file for what those four files
contain and why they are kept.

## Strategy

The structural scaffold is verified with no analytic machinery: divisibility/gcd
algebra, totient multiplicativity, induction over the prime base, linear/nonlinear
arithmetic (`omega`, `nlinarith`), and finite-set cardinality (union bound).
On the window `(P_max, P_min·P_max]`, "uncovered" and "prime" coincide exactly
(`LPF.lean`'s `prime_iff_uncovered_general`): the forward direction is the
`minFac`-of-a-prime fact, the backward direction is the least-prime-factor
bound (Lemma 3.1) — coverage is by the full base, every prime `≤ P_max`
(Definition 2.1), so this holds for the fixed reach `2·P_max` and for any
other positive scaling `P_min·P_max` alike; `P_min` is a window-width
multiplier here, not a lower cutoff on which primes count as covering.
`SelfContained.lean` separately establishes that `P_min·P_max` is always a
self-contained reach for the window's *size*, a distinct fact about the
window's boundary, not about which elements in it are prime.
The postulate collapses to a single quantitative atom — *the sieve never covers
its own window* — closed by the self-contained argument on the central binomial
coefficient (`binomial_contradiction`, `BinomialCertificate.lean`): the
factorization upper bound on `C(2n,n)` reproved in-project from Legendre/Kummer
+ primorial (`BinomialBound.lean`), combined with the threshold inequality
(`Threshold.lean`) and Mathlib's own central-binomial lower bound; a
computational oracle handles `n < 512`.

### Key constraint (Definition 2.1)
The prime base `𝒫` must be a *complete generative segment*: it contains every prime
between `P_min` and `P_max` without exception.  Omitting one prime breaks the identity
φ(M)/M = ∏(1−1/p) and invalidates the multiplicative structure.

### Chain
1. **LPF** (`LPF.lean`): every composite n ∈ (P_max, P_min·P_max] has n.minFac ≤ P_max,
   so uncovered elements must be prime; packaged as the equivalence
   `prime_iff_uncovered_general`, for any positive window-scaling factor P_min.  [verified]

2. **Zero Effective Force** (`ZeroForce.lean`): P_k's only multiple in (P_k, 2·P_k] is
   2·P_k, already covered by 2 ∈ 𝒫'.  Composites in the window ↔ covered by 𝒫'.  [verified]

3. **Structural Weight** (`Weight.lean`): w(𝒫) = P_k·φ(M)/M ≥ 1, by induction; preceding
   base satisfies M' < P_k·φ(M').  This is the *average* survivor density — a necessary
   condition, **not** by itself a guarantee for a specific window.  [verified]

4. **Self-containment** (`SelfContained.lean`): the window width ≤ P_max (multiplier = the
   minimal prime) is always a self-contained width, fixed by the base's own extremes and
   independent of the irregular gap to the next prime — not a claim that it is the widest
   such width — generalized to any base minimum `m` (`window_self_contained_bound_general`,
   `self_contained_bound_independent_of_gap`). A separate fact about the window's *size*,
   not part of the Palomar excerpt.  [verified]

5. **Central Positivity** (`BinomialBound.lean`, `Threshold.lean`,
   `BinomialCertificate.lean`, `GPS_StateMachine.lean`):
   `binomial_contradiction` closed self-containedly — computational oracle for 2 < n < 512,
   the two bounds on `C(2n,n)` for n ≥ 512 (no Bertrand import); `dense_sieve_survivor` follows,
   since a prime in the window is automatically free. [verified]

6. **Reduction** (`Main.lean`): `structural_bertrand_chebyshev` and `bertrand_chebyshev`.
   [verified]

## File structure

| File | Content | Status |
|------|---------|--------|
| `Defs.lean`            | Complete generative base, sieve coverage, window (Def. 2.1) | verified |
| `LPF.lean`             | Least Prime Factor; uncovered ⇒ prime (Lemma 3.1); uncovered ⇔ prime on any positively-scaled window (Cor. 3.3, `prime_iff_uncovered_general`) | verified |
| `ZeroForce.lean`       | Zero Effective Force; composites covered by 𝒫' (Lemma 4.1) | verified |
| `Weight.lean`          | Structural weight w ≥ 1; M' < P·φ(M') (Lemma 4.3) | verified |
| `SelfContained.lean`   | Self-containment fixes the window reach (why the constant) | verified |
| `Truncated.lean`       | Sparse-regime positivity by union bound | verified |
| `BinomialBound.lean`   | Upper bound `window_centralBinom_le` from primitives (no Bertrand import) | verified |
| `Threshold.lean`       | Prime-free size inequality `threshold_inequality` (convexity) | verified |
| `BinomialCertificate.lean` | Self-contained kernel `binomial_contradiction` | verified |
| `GPS_StateMachine.lean`| Generative window; regime dispatch; `prime_in_window` | verified |
| `Main.lean`            | Theorem 5.1 + `bertrand_chebyshev` | verified |

## Extended development (verified, but not part of the Palomar excerpt)

The four files below are fully verified — zero `sorry`, same trust base as
everything above — but are separate, self-standing results, not exercised by
`bertrand_chebyshev`'s own proof term. They are not part of the narrow
`Challenge.lean`/`Solution.lean` excerpt reviewed by Palomar (that excerpt
never imports any of these four, with or without them present here); they are
kept because they are genuine, separately-proved mathematics from the same
research program, described in full in the accompanying paper.

| File | Content | Status |
|------|---------|--------|
| `Rings.lean` | Ring collective: void/coverage dichotomy generalized to the full deterministic zone `(P_k, P_k²)` (`void_iff_prime_in_deterministic_zone`), with `determinism_breaks_above` showing that reach exact; minFac telescope, interference (Legendre) identity, generalized family `(P_max, P_min·P_max]`; small-anchor closures `P_k ≤ 83`; S1 bridge to `C(2n,n)` | verified, off-path |
| `Newton.lean` | A second derivation of the central binomial coefficient's window content — S1 divisibility, lower bound `4^n ≤ (2n+1)·C(2n,n)` from the Pascal row | verified, off-path |
| `Certificate.lean` | Modular interface `WindowCertificate`; instances `erdos_certificate` (via Mathlib) and `binomial_certificate` (self-contained) — modularity as a theorem | verified, off-path |
| `Erdos.lean` | Instance A: `erdos_contradiction` via Mathlib's two `C(2n,n)` inequalities — the one file in this repository that imports `Mathlib.NumberTheory.Bertrand`, kept only for the modularity comparison | verified, off-path |
-/
