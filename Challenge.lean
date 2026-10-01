module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Finset.Basic

/-!
# Advertised statements

This is the small, trusted surface a mathematical reader should audit. It contains one
declaration: Bertrand's postulate in its Chebyshev-strengthened form.

`Submission.bertrand_chebyshev` — for every integer `N > 1` there is a prime strictly
greater than `N` and at most `2 * N`. This is a classical theorem (Bertrand 1845, Chebyshev
1852), proved here by an independent, from-scratch route: a structural sieve against the
primorial of preceding primes (described in the accompanying paper, `LaTex/The Structural
Sieve.pdf`), closed quantitatively by a self-contained central-binomial-coefficient argument
(`BinomialCertificate.lean`) that does not depend on `Mathlib.NumberTheory.Bertrand`. Bertrand
asked "is there a prime here?"; this project's proof route asks "what can a fixed, finite
sieve base build, and what does it leave standing?" — the central binomial coefficient is the
same object Erdős used for his own, differently-motivated proof of the same postulate.

This file itself deliberately imports nothing from `StructuralSieve/` — only Mathlib. A
canonical challenge file must be checkable in isolation, independent of the submitter's own
library.

## Why only this one declaration is advertised here

The structural sieve this proof is built on also yields two elementary characterizations of
primality by sieve-coverage (`StructuralSieve.prime_iff_uncovered_by_prev` and its
width-generalized form, both in `StructuralSieve/`) — but, on their own, those are a direct
restatement of the classical trial-division criterion (a composite `n` has a prime factor at
most `√n`) against a divisor set fixed in advance rather than searched fresh for each `n`.
That restatement is real, used internally by this development, and documented in the
accompanying paper and README — but it is not independently novel content, so it is not
submitted here as its own Comparator-checked headline result. Only the theorem that is
independently defensible as substantive — an original, from-scratch proof route for a
classical theorem, avoiding Mathlib's own Bertrand development entirely — is advertised.
-/

/-- **Bertrand–Chebyshev bound**, proved by an independent structural-sieve route (not using
`Mathlib.NumberTheory.Bertrand`). For every `N > 1` there is a prime `p` with
`N < p ≤ 2 * N`. -/
public theorem Submission.bertrand_chebyshev (N : ℕ) (hN : 1 < N) :
    ∃ p : ℕ, N < p ∧ p ≤ 2 * N ∧ p.Prime := by
  sorry
