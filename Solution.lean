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

theorem Submission.bertrand_chebyshev (N : ℕ) (hN : 1 < N) :
    ∃ p : ℕ, N < p ∧ p ≤ 2 * N ∧ p.Prime :=
  StructuralSieve.bertrand_chebyshev N hN
