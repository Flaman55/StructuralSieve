import StructuralSieve.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
/-!
# LPF.lean — Lemma 3.1: Least Prime Factor

Every composite `n ∈ (P_max, P_min · P_max]` satisfies `n.minFac ≤ P_max`.

**Proof**: Write `n = p(n) · m(n)` with `p(n) ≤ m(n)`.  Then
  `p(n)² ≤ p(n) · m(n) = n ≤ P_min · P_max ≤ P_max²`,
so `p(n) ≤ P_max`.  Since the base contains ALL primes ≤ P_max
(Definition 2.1), `p(n) ∈ 𝒫`.

**Corollary**: Any element of the window not covered by the sieve must be prime.
-/

namespace StructuralSieve

/-! ## Lemma 3.1 -/

/--
**Lemma 3.1** (Least Prime Factor).

If `n ∈ (P_max, P_min · P_max]` is composite, then `n.minFac ≤ P_max`.

The proof uses only: `n.minFac ^ 2 ≤ n` (standard) and `n ≤ P_min · P_max ≤ P_max²`.
-/
theorem least_prime_factor_bound
    {P_min P_max : ℕ}
    (hPmin_pos : 0 < P_min)
    (hPmin_le  : P_min ≤ P_max)
    {n : ℕ}
    (_hn_lo  : P_max < n)
    (hn_hi   : n ≤ P_min * P_max)
    (hn2     : 2 ≤ n)
    (hn_comp : ¬ n.Prime) :
    n.minFac ≤ P_max := by
  -- Step 1: n.minFac ^ 2 ≤ n  (standard: minFac ≤ cofactor for composites)
  have hf2 : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hn_comp
  -- Step 2: n ≤ P_max ^ 2  (because P_min ≤ P_max)
  have hn_Pmax2 : n ≤ P_max ^ 2 := by
    calc n ≤ P_min * P_max := hn_hi
         _ ≤ P_max * P_max := Nat.mul_le_mul_right P_max hPmin_le
         _ = P_max ^ 2     := (sq P_max).symm
  -- Step 3: n.minFac ^ 2 ≤ P_max ^ 2, hence n.minFac ≤ P_max
  have hf_Pmax2 : n.minFac ^ 2 ≤ P_max ^ 2 := le_trans hf2 hn_Pmax2
  nlinarith [sq_nonneg n.minFac, sq_nonneg P_max]

/--
**Corollary 3.2** (Uncovered elements are prime).

Any `n ∈ (P_max, P_min · P_max]` with `n.minFac > P_max` must be prime.
-/
theorem uncovered_is_prime
    {P_min P_max : ℕ}
    (hPmin_pos : 0 < P_min)
    (hPmin_le  : P_min ≤ P_max)
    {n : ℕ}
    (hn_lo    : P_max < n)
    (hn_hi    : n ≤ P_min * P_max)
    (hn2      : 2 ≤ n)
    (huncov   : ¬ SieveCovered P_max n) :
    n.Prime := by
  -- If n were composite, LPF gives n.minFac ≤ P_max, contradicting huncov
  by_contra hn_comp
  exact huncov (least_prime_factor_bound hPmin_pos hPmin_le hn_lo hn_hi hn2 hn_comp)

/--
**Corollary 3.3** (Uncovered ↔ prime, on a window scaled by any factor `P_min`).

Generalizes `ZeroForce.lean`'s `prime_iff_uncovered_by_prev` (window `(P_k, 2·P_k]`, upper
reach fixed at `2·P_k`) to a window `(P_max, P_min·P_max]` whose upper reach is scaled by
any positive `P_min ≤ P_max` instead of the fixed factor `2`. Coverage is still by the same
full base as everywhere else in this file — every prime `≤ P_max` (Definition 2.1) — so
`P_min` names a window-width multiplier here, not a lower cutoff on which primes count as
covering. `n` is prime iff `n` is *not* covered by that base — the same structural invariant
as theorem 1 ("what the base cannot build is exactly what is prime"), restated on a window
whose reach is a free parameter instead of fixed at `2·P_max`.

Both directions were already available separately (the forward direction is the same
`minFac`-of-a-prime argument `ZeroForce.lean` uses; the backward direction is
`uncovered_is_prime` above, already proved for this general window) — this packages them as
the single equivalence.
-/
theorem prime_iff_uncovered_general
    {P_min P_max : ℕ}
    (hPmin_pos : 0 < P_min)
    (hPmin_le  : P_min ≤ P_max)
    {n : ℕ}
    (hn_lo : P_max < n)
    (hn_hi : n ≤ P_min * P_max)
    (hn2   : 2 ≤ n) :
    n.Prime ↔ ¬ SieveCovered P_max n := by
  constructor
  · -- prime → uncovered: a prime > P_max has minFac = itself > P_max
    intro hn_prime
    simp only [SieveCovered, not_le]
    rw [Nat.Prime.minFac_eq hn_prime]
    exact hn_lo
  · -- uncovered → prime: Corollary 3.2, for general P_min
    intro huncov
    exact uncovered_is_prime hPmin_pos hPmin_le hn_lo hn_hi hn2 huncov

end StructuralSieve
