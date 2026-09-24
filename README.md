# All four Liouville sign patterns in binary sums: Lean formalization

Let λ(n) = (−1)^Ω(n) be the Liouville function. This repository contains a Lean 4 / mathlib proof of:

**Theorem.** Every integer N ≥ 2 outside {2, 3, 4, 5, 6, 9, 10} can be written as N = a + b with a, b ≥ 1 and (λ(a), λ(b)) equal to any prescribed pair in {+1, −1}². Each of the seven exceptions misses at least one pattern.

```lean
theorem OddCase.all_four_patterns_unconditional {N : ℕ} (hN : 2 ≤ N)
    (h2 : N ≠ 2) (h3 : N ≠ 3) (h4 : N ≠ 4) (h5 : N ≠ 5) (h6 : N ≠ 6)
    (h9 : N ≠ 9) (h10 : N ≠ 10) {s t : ℤ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) : OddCase.SignPair N s t
```

`SignPair N s t` means `∃ a b, 0 < a ∧ 0 < b ∧ a + b = N ∧ liouville a = s ∧ liouville b = t`, where `liouville` is mathlib's `ArithmeticFunction.liouville`. The statement carries no hypothesis beyond the range and the exceptions, and `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`.

The same argument, applied to an arbitrary completely multiplicative `f : ℕ → {±1}`, shows that the Legendre symbol is the only obstruction at primes:

**Theorem F.** Let `f` be completely multiplicative with values `±1` and `f(2) = f(3) = -1`. If `f(5) = -1` and a prime `p ≥ 11` has no `a + b = p` with `f(a) = f(b) = ε`, then `p ≡ 3 (mod 4)` and `f(n) = (n/p)` for `0 < n < p/2`. If a prime `p ≥ 7` has no `a + b = p` with `f(a) ≠ f(b)`, then `p ≡ 1 (mod 4)` and `f(n) = (n/p)` for `0 < n < p/2`.

Both conclusions are attained: for p = 43, 67, 163 the completely multiplicative extension of `(·/p)` has no equal pair at p, and for p = 29, 101 it has no unequal pair.

The accompanying paper is *All four Liouville sign patterns occur in the binary decompositions of every integer N ≥ 11* (L. Meng), which explains the mathematics.

## Main declarations

| Declaration | Content |
|---|---|
| `OddCase.all_four_patterns_unconditional` | the theorem above |
| `OddCase.equal_pair_at_prime` | every prime p ≥ 5 is a + b with λ(a) = λ(b) = ε, for each ε = ±1 |
| `OddCase.OneExcl.exact_bands` | one-exclusion rigidity at an odd modulus p with 3 ∤ p, 7 ∤ p (dilation laws for 2, 3, 5) |
| `OddCase.mixedPair_of_ge` | every N ≥ 11 has a pair with λ(a) ≠ λ(b) |
| `OddCase.legendre_of_no_equal_pair` | Theorem F, equal patterns: a missing (ε, ε) pair at a prime p ≥ 11 forces f = (·/p) on (0, p/2), p ≡ 3 (mod 4) |
| `OddCase.legendre_of_no_mixed_pair` | Theorem F, mixed patterns: a missing unequal pair at a prime p ≥ 7 forces f = (·/p) on (0, p/2), p ≡ 1 (mod 4) |
| `OddCase.mangerel_nonextremality` | \|∑_{a<N} λ(a)λ(N−a)\| < N − 1 for N ≥ 11 (Mangerel, IMRN 2024, Thm 1.2), re-derived |
| `SignPatterns.positivePair_even` | every even N ∉ {4, 6} is a + b with λ(a) = λ(b) = 1 |
| `OddCase.not_pair_two`, …, `OddCase.not_mixed_ten` | the seven exceptions are sharp |

## Dependencies

This project builds on the Lean development of [CaptainSude/Liouville-Goldbach](https://github.com/CaptainSude/Liouville-Goldbach) (every even N > 2 is a sum of two integers with λ = −1; the 2p theorem; the extension lemma; the small-prime lemma). That repository is **not copied here**: Lake fetches it at the pinned release commit `da3c528c16975781e21f3b7270c61331e70da8d2`.

Pinned versions: Lean `v4.34.0-rc2`, mathlib `de2ef68216c6074f338c8e61890ee0a379ddfb9b`.

## Build

```sh
lake update
lake exe cache get
lake build
lake env lean Audit.lean
```

On some Linux machines `lake exe cache get` needs a higher open-file limit (`ulimit -n 65536`).

## Layout

| File | Content |
|---|---|
| `SignPatterns.lean` | (+,+) at even totals; sharpness at 2, 4, 6, 10 |
| `OddCase/Core.lean` | the one-exclusion setting, defects, nonnegativity, the four-range identities |
| `OddCase/Sums.lean` | support of the doubling defect (summation argument) |
| `OddCase/Phi.lean` | the map Φ, the local ×5 argument, the well-founded induction, `exact_bands` |
| `OddCase/Main.lean` | bridge to the odd completion; equal pairs at primes |
| `OddCase/Patterns.lean` | odd totals, the four patterns (with Mangerel's theorem as a hypothesis), sharpness |
| `OddCase/Mixed.lean` | unequal pairs without Mangerel; the unconditional theorem |
| `OddCase/General.lean` | Theorem F for arbitrary completely multiplicative f |
| `Audit.lean` | statements and axiom audit |
