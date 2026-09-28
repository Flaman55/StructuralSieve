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
2. `Submission.window_reach_self_contained` — why the reach is `2·P_max` and not some other
   multiplier. This is not an existence question and not a divisor-search bound; it is a
   closure condition on the sieve's own *generative* process. The sieve feeds itself: new
   primes found in the window extend the base, the extended base extends the next window, and
   so on. For that hand-off to be well-formed, one round's window cannot reach so far that a
   prime `q` it just found has its own least proper multiple `2·q` fall back *inside the same
   window* — that would require the round to treat `q` simultaneously as a new discovery
   (not yet in the base) and as already covered (by `q` itself, as if it already were). Concrete
   collision at width `3·P_max`: base `{2,3,5}`, window `(5,15]` — this contains both the new
   prime `7` and `7`'s own boundary multiple `14 = 2·7`, at once. `2·P_max` is exactly the
   widest reach at which this self-reference cannot occur. This is the same closure condition,
   stated for a base whose minimum element is any `m` (not only `2`): the least proper multiple
   of a new window element is `m·q`, and `hi ≤ m·P` is exactly the condition under which that
   multiple always falls outside the window `(P, hi]` — specializing to `2·P_max` at `m = 2`
   (`SelfContained.lean`'s `window_self_contained_bound_general` and
   `max_self_contained_bound_general`, which specialize to `window_self_contained_bound` and
   `max_self_contained_width` at `m = 2`).
3. `Submission.bertrand_chebyshev` — Bertrand's postulate in its Chebyshev-strengthened form
   (for every integer `N > 1` there is a prime strictly greater than `N` and at most `2 * N`).
   This is a **corollary of the same sieve mechanism (1) and (2) describe**, not of either
   equivalence by name: (1) shows a window survivor (uncovered by the preceding base) is
   prime; (2) fixes the window's reach; what remains is existence — that the window is not
   *entirely* covered — which the quantitative closure supplies
   (`BinomialCertificate.lean`'s self-contained central-binomial argument, not depending on
   `Mathlib.NumberTheory.Bertrand`). The proof term itself goes through the sieve's own
   survivor lemma (`GPS_StateMachine.lean`'s `prime_in_window`), not through
   `prime_iff_uncovered_by_prev` by name — that equivalence is a separate, standalone result,
   proved for its own sake, not a lemma this proof calls. Bertrand asked "is there a prime
   here?"; this project asked "where does deterministic certainty about primality end, and
   why does the window have exactly this reach?" — different questions, proved by different
   means, that happen to agree on this object.

All three are discharged in `Solution.lean` by invoking the fully independent structural
development in this repository's `StructuralSieve/` directory. That development does
**not** import `Mathlib.NumberTheory.Bertrand`; the quantitative core for (3) is an original
structural sieve described in the accompanying paper (`LaTex/The Structural Sieve.pdf`).

This file itself deliberately imports nothing from `StructuralSieve/` — only Mathlib. A
canonical challenge file must be checkable in isolation, independent of the submitter's own
library, so (1) below states its project-specific predicate unfolded to what it literally
means rather than by name: `StructuralSieve.SieveCovered P n` is `n.minFac ≤ P` (`Defs.lean`).
The two forms are definitionally equal, so a proof term from the named version still checks
against this unfolded statement — but Palomar's comparator does a literal statement match
rather than a `defeq` check, so `Solution.lean` restates (1) here verbatim, unfolded, and only
calls the named version inside the proof term. (2) is pure arithmetic on naturals, with no
project-specific predicate to unfold.
-/

/-- **Original question: is every composite in the window covered by the preceding base?**
For a prime `P_k` and `n ∈ (P_k, 2·P_k]`, `n` is prime iff `n` is not covered by the base of
primes below `P_k` (`n.minFac ≤ P_k`). Proved by exact divisibility, not by counting. -/
theorem Submission.prime_iff_uncovered_by_prev
    {P_k : ℕ} (hP : Nat.Prime P_k) {n : ℕ}
    (hn_lo : P_k < n) (hn_hi : n ≤ 2 * P_k) (hn2 : 2 ≤ n) :
    n.Prime ↔ ¬ (n.minFac ≤ P_k) := by
  sorry

/-- **Why the reach is `2·P_max`: a closure condition on the sieve's own generative process,
not an existence bound and not a divisor-search bound.** The sieve feeds itself — a new prime
found in one window extends the base for the next. For that hand-off to be well-formed, no
window may reach so far that a prime `q` it just found has its own least proper multiple
`2·q` fall back inside that same window (which would force the round to treat `q` both as a
fresh discovery and as already covered by itself). `2·P_max` is exactly the widest reach at
which this self-reference cannot occur: for a base whose minimum element is any `m` (`m = 2`
is the standard case), the least proper multiple of a new window element `q ∈ (P, hi]` is
`m·q`, and `hi ≤ m·P` is exactly the condition under which that multiple always falls
strictly outside the window. -/
theorem Submission.window_reach_self_contained
    {P hi q m : ℕ} (hm : 1 ≤ m) (hhi : hi ≤ m * P) (hq_lo : P < q) (_hq_hi : q ≤ hi) :
    hi < m * q := by
  sorry

/-- **Bertrand–Chebyshev bound** (corollary of the sieve mechanism (1) and (2) describe
jointly, not of either by name). For every `N > 1` there is a prime `p` with
`N < p ≤ 2 * N`. -/
theorem Submission.bertrand_chebyshev (N : ℕ) (hN : 1 < N) :
    ∃ p : ℕ, N < p ∧ p ≤ 2 * N ∧ p.Prime := by
  sorry
