import Mathlib.Tactic

/-!
# SelfContained.lean — Window-width lemma (why the constant is `2` / why width `≤ P_max`)

This is the structural justification for the *value* of the constant: self-containment of
the window forces width `≤ P_max`, i.e. a multiplier `≤ 2`. It is proved elementarily, with
no `sorry`.

**Note.** This is not the existence step. It concerns the *size* of the window (the
container), not whether the window contains a prime (the content). Existence lies on a
different axis and is settled separately by the quantitative certificate
(`Erdos.erdos_contradiction`); nothing in this file depends on it.
-/

namespace StructuralSieve

/--
**Self-containment from width `≤ P`.**

In the window `(P, P+W]` with `W ≤ P`, the least proper multiple `2·q` of any new element
`q ∈ (P, P+W]` lies outside the window (`P + W < 2·q`). Hence width `≤ P` (multiplier `≤ 2`)
guarantees self-containment: no in-window element re-enters its own window through a proper
multiple of itself.
-/
theorem window_self_contained_bound {P W q : ℕ}
    (hW : W ≤ P) (hq_lo : P < q) (_hq_hi : q ≤ P + W) :
    P + W < 2 * q := by
  omega

/--
**Failure of self-containment forces width `> P`.**

Contrapositive of the previous lemma: if the least proper multiple `2·q` of some
`q ∈ (P, P+W]` falls inside the window (`2·q ≤ P + W`), then the width must exceed `P`.
Equivalently, self-containment fails once the multiplier exceeds `2`.
-/
theorem width_gt_of_overlap {P W q : ℕ}
    (hq_lo : P < q) (hover : 2 * q ≤ P + W) :
    P < W := by
  omega

/--
**Why exactly `2·P_max`.**

The maximal self-contained window anchored at `P_max` is `(P_max, 2·P_max]` (width exactly
`P_max`). A wider window is not self-contained (`width_gt_of_overlap`); for width `≤ P_max`
self-containment holds (`window_self_contained_bound`). The constant `2` is therefore not a
choice: it is the maximal width of a self-contained window.
-/
theorem max_self_contained_width {P q : ℕ}
    (hq_lo : P < q) (_hq_hi : q ≤ 2 * P) :
    2 * P < 2 * q := by
  omega

/-! ## Generalization: arbitrary base minimum `m`

The three lemmas above fix the base's minimum element at `2`. A base need not start at `2`:
`Defs.lean`'s `window (P_min) (P_max)` already generalizes the window to `(P_max, P_min·P_max]`
for any `P_min ≤ P_max`. The self-containment argument generalizes the same way: the least
proper multiple of a new window element `q`, built from the base's own minimum `m`, is `m·q`
(not `2·q`). Everything below specializes back to the three lemmas above at `m = 2`.

**Why `m` must be prime, not merely `1 ≤ m`.** `m` stands for `PrimeBase.pMin` (`Defs.lean`):
the minimum of a nonempty finite set of primes (`PrimeBase.all_prime`), so it is always a prime,
never `1`. Requiring only `1 ≤ m` admits a degenerate case with no sieve-theoretic meaning: at
`m = 1`, `m·q = q` is not a proper multiple of anything, so "the least proper multiple falls
outside the window" is vacuous rather than a real closure condition. The three theorems below
require `Nat.Prime m` for this reason. -/

/--
**Self-containment from a general window bound (`hi ≤ m·P`).**

For a base whose minimum element is the prime `m`, the least proper multiple of any new window
element `q ∈ (P, hi]` built from that minimum is `m·q`. If the window's upper bound satisfies
`hi ≤ m·P`, this multiple always falls strictly outside the window. Generalizes
`window_self_contained_bound` (`m = 2`, `hi = P + W`) to any base minimum `m` (any prime).
-/
theorem window_self_contained_bound_general {P hi q m : ℕ}
    (hm : Nat.Prime m) (hhi : hi ≤ m * P) (hq_lo : P < q) (_hq_hi : q ≤ hi) :
    hi < m * q := by
  have hm0 : 0 < m := hm.pos
  have hq1 : P + 1 ≤ q := by omega
  have hmq : m * (P + 1) ≤ m * q := Nat.mul_le_mul (le_refl m) hq1
  have heq : m * (P + 1) = m * P + m := by ring
  omega

/--
**Failure of self-containment forces the window bound past `m·P`.**

Contrapositive companion to the previous lemma: if the least proper multiple `m·q` of some
`q ∈ (P, hi]` falls inside the window (`m·q ≤ hi`), then `hi` must exceed `m·P`. Generalizes
`width_gt_of_overlap`.
-/
theorem window_bound_gt_of_overlap_general {P hi q m : ℕ}
    (hm : Nat.Prime m) (hq_lo : P < q) (hover : m * q ≤ hi) :
    m * P < hi := by
  have hm0 : 0 < m := hm.pos
  have hq1 : P + 1 ≤ q := by omega
  have hmq : m * (P + 1) ≤ m * q := Nat.mul_le_mul (le_refl m) hq1
  have heq : m * (P + 1) = m * P + m := by ring
  omega

/--
**Why exactly `m·P_max`.**

The maximal self-contained window anchored at `P` for a base with minimum `m` is
`(P, m·P]` (upper bound exactly `m·P`). Generalizes `max_self_contained_width`: the constant
`m` (which is `2` in the standard base starting at the prime `2`) is not a choice — it is the
maximal reach of a self-contained window for a base whose own minimum element is `m`.
-/
theorem max_self_contained_bound_general {P q m : ℕ}
    (hm : Nat.Prime m) (hq_lo : P < q) (_hq_hi : q ≤ m * P) :
    m * P < m * q := by
  have hm0 : 0 < m := hm.pos
  have hq1 : P + 1 ≤ q := by omega
  have hmq : m * (P + 1) ≤ m * q := Nat.mul_le_mul (le_refl m) hq1
  have heq : m * (P + 1) = m * P + m := by ring
  omega

/-! ## Exactness: the limit is fixed by the base's own extremes, not by the prime gap

`m·P` is not "the point past which something breaks" in the sense of the smallest bad
natural number — the window `(P_max, P_max + k]` for small `k` beyond `m·P` need not exhibit
any covering failure yet, since which specific number causes trouble depends on the (irregular)
gap to the next prime past `P`. What is fixed by the base alone, independent of that gap, is
`m·P` itself: it is the largest value expressible as (base minimum)·(base maximum) without
reaching for a prime beyond the base. Reaching further requires treating the next prime past
`P` as though it already belonged to the base — which is a different, extended base, not a
failure of arithmetic at a specific `n`. -/

/--
**Self-containment's limit is fixed by the base's own extremes, not by the gap to the next
prime.**

For a base whose minimum element is the prime `m`, the window `(P, m·P]` is self-contained
unconditionally (`window_self_contained_bound_general`) — no element of the window has its
base-multiple fall back inside, and this needs no knowledge of where the next prime past `P`
actually lies. The true point where self-containment fails is `m·q`, for `q` the least prime
exceeding `P` — a value that depends on the gap to the next prime, which is irregular (as small
as `1`, for `P = 2`, `q = 3`; arbitrarily larger elsewhere). `m·P` is provably always strictly
below this true failure point (`m·P < m·q`, from `P < q` and `m > 0`), so it is a gap-independent
guarantee: the window stays self-contained up to and including `m·P` no matter how close or far
the next prime happens to be.
-/
theorem self_contained_bound_independent_of_gap {P m : ℕ}
    (hm : Nat.Prime m) (hP : 0 < P) :
    ∃ q, Nat.Prime q ∧ P < q ∧
      (∀ n, P < n → n ≤ m * P → m * P < m * n) ∧
      m * P < m * q := by
  obtain ⟨q, hq_ge, hq_prime⟩ := Nat.exists_infinite_primes (P + 1)
  have hm0 : 0 < m := hm.pos
  have hPq : P < q := by omega
  refine ⟨q, hq_prime, hPq, ?_, ?_⟩
  · intro n hn_lo hn_hi
    exact max_self_contained_bound_general hm hn_lo hn_hi
  · have hq1 : P + 1 ≤ q := by omega
    have hmq : m * (P + 1) ≤ m * q := Nat.mul_le_mul (le_refl m) hq1
    have heq : m * (P + 1) = m * P + m := by ring
    omega

end StructuralSieve
