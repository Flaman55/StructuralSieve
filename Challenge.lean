import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic

/-!
# Advertised statements

This is the small, trusted surface a mathematical reader should audit. It contains three
declarations, in decreasing order of what motivated this development and increasing order
of fame:

1. `Submission.prime_iff_uncovered_by_prev` — the original question this project set out to
   answer. Not "does a prime exist in `(P_k, 2·P_k]`?" (Bertrand's question) but "is every
   composite in that window already covered by a prime strictly below `P_k` (or by `2`)? —
   i.e. does the window need any prime factor from *outside* itself?" The answer is an exact
   equivalence, not an existence bound: `n` is prime iff `n` is *not* covered by the base of
   primes below `P_k`. This is proved directly from divisibility (`ZeroForce.lean`'s Zero
   Effective Force lemma plus the least-prime-factor bound), with no appeal to counting or to
   the central binomial coefficient.
2. `Submission.prime_iff_uncovered_by_prev_general` — the same equivalence as (1), for a
   base whose minimum element need not be `2`. A window `(P_max, P_min·P_max]` built from a
   base with smallest element `P_min` (not necessarily `2`) has the identical structure: `n`
   is prime iff `n` is *not* covered by the base below `P_max` (`n.minFac ≤ P_max`). This is
   not a different phenomenon from (1) that happens to resemble it — it is the same
   structural invariant, "what the base cannot build is exactly what is prime," restated at
   whatever minimum the base actually starts from. (1) is the special case `P_min = 2`.
   Proved the same way: the forward direction is the `minFac`-of-a-prime fact `ZeroForce.lean`
   already uses for (1); the backward direction is `LPF.lean`'s least-prime-factor bound,
   which was already stated for a general base minimum.
3. `Submission.bertrand_chebyshev` — Bertrand's postulate in its Chebyshev-strengthened form
   (for every integer `N > 1` there is a prime strictly greater than `N` and at most `2 * N`).
   This is a **corollary of the sieve's survivor mechanism**, the same "uncovered = prime"
   invariant (1) and (2) state at two different base minimums — not a corollary of either
   result by name, and not built by literally chaining (1) or (2) as proof-term lemmas: the
   proof term goes through the sieve's own survivor lemma (`GPS_StateMachine.lean`'s
   `prime_in_window`) and a separate quantitative closure (`BinomialCertificate.lean`'s
   self-contained central-binomial argument, not depending on `Mathlib.NumberTheory.Bertrand`),
   neither of which invokes `prime_iff_uncovered_by_prev` or
   `prime_iff_uncovered_by_prev_general` by name — both are separate, standalone results,
   proved for their own sake, not lemmas this proof calls. Bertrand asked "is there a prime
   here?"; this project asked "what can the base build, and what does it leave standing?" —
   different questions, proved by different means, that happen to agree on this object.

All three are discharged in `Solution.lean` by invoking the fully independent structural
development in this repository's `StructuralSieve/` directory. That development does
**not** import `Mathlib.NumberTheory.Bertrand`; the quantitative core for (3) is an original
structural sieve described in the accompanying paper (`LaTex/The Structural Sieve.pdf`).

This file itself deliberately imports nothing from `StructuralSieve/` — only Mathlib. A
canonical challenge file must be checkable in isolation, independent of the submitter's own
library, so (1) and (2) below state their project-specific predicate unfolded to what it
literally means rather than by name: `StructuralSieve.SieveCovered P n` is `n.minFac ≤ P`
(`Defs.lean`). The two forms are definitionally equal, so a proof term from the named version
still checks against this unfolded statement — but Palomar's comparator does a literal
statement match rather than a `defeq` check, so `Solution.lean` restates (1) and (2) here
verbatim, unfolded, and only calls the named versions inside the proof term.
-/

/-- **Original question: is every composite in the window covered by the preceding base?**
For a prime `P_k` and `n ∈ (P_k, 2·P_k]`, `n` is prime iff `n` is not covered by the base of
primes below `P_k` (`n.minFac ≤ P_k`). Proved by exact divisibility, not by counting. -/
theorem Submission.prime_iff_uncovered_by_prev
    {P_k : ℕ} (hP : Nat.Prime P_k) {n : ℕ}
    (hn_lo : P_k < n) (hn_hi : n ≤ 2 * P_k) (hn2 : 2 ≤ n) :
    n.Prime ↔ ¬ (n.minFac ≤ P_k) := by
  sorry

/-- **Same invariant as (1), for a base with any minimum element `P_min` (not only `2`).**
For a window `(P_max, P_min·P_max]` built from a base whose smallest element is `P_min`, `n`
is prime iff `n` is not covered by the base below `P_max` (`n.minFac ≤ P_max`). (1) is the
special case `P_min = 2`. Proved by exact divisibility, the same as (1). -/
theorem Submission.prime_iff_uncovered_by_prev_general
    {P_min P_max : ℕ} (hPmin_pos : 0 < P_min) (hPmin_le : P_min ≤ P_max)
    {n : ℕ} (hn_lo : P_max < n) (hn_hi : n ≤ P_min * P_max) (hn2 : 2 ≤ n) :
    n.Prime ↔ ¬ (n.minFac ≤ P_max) := by
  sorry

/-- **Bertrand–Chebyshev bound** (corollary of the sieve mechanism (1) and (2) describe
jointly, not of either by name). For every `N > 1` there is a prime `p` with
`N < p ≤ 2 * N`. -/
theorem Submission.bertrand_chebyshev (N : ℕ) (hN : 1 < N) :
    ∃ p : ℕ, N < p ∧ p ≤ 2 * N ∧ p.Prime := by
  sorry
