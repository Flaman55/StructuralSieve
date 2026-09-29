import StructuralSieve.Main
import StructuralSieve.SelfContained

/-!
# Proved solutions

This module imports the full structural proof development. Comparator checks that each
declaration below has exactly the same statement as its counterpart in `Challenge.lean` and
uses only the permitted axioms.

Each proof is a one-line restatement: the real work happens in `StructuralSieve/`, which
is derived entirely from the structural sieve described in the accompanying paper without
depending on `Mathlib.NumberTheory.Bertrand`. That development contains zero `sorry`s and
(per `#print axioms`) depends only on `propext`, `Classical.choice`, and `Quot.sound` — no
`native_decide`/`Lean.ofReduceBool`.
-/

theorem Submission.prime_iff_uncovered_by_prev
    {P_k : ℕ} (hP : Nat.Prime P_k) {n : ℕ}
    (hn_lo : P_k < n) (hn_hi : n ≤ 2 * P_k) (hn2 : 2 ≤ n) :
    n.Prime ↔ ¬ (n.minFac ≤ P_k) :=
  StructuralSieve.prime_iff_uncovered_by_prev hP hn_lo hn_hi hn2

theorem Submission.window_reach_self_contained
    {P hi q m : ℕ} (hm : Nat.Prime m) (hhi : hi ≤ m * P) (hq_lo : P < q) (_hq_hi : q ≤ hi) :
    hi < m * q :=
  StructuralSieve.window_self_contained_bound_general hm hhi hq_lo _hq_hi

theorem Submission.bertrand_chebyshev (N : ℕ) (hN : 1 < N) :
    ∃ p : ℕ, N < p ∧ p ≤ 2 * N ∧ p.Prime :=
  StructuralSieve.bertrand_chebyshev N hN
