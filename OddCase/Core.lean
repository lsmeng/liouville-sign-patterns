import Mathlib

/-!
# One-exclusion rigidity at an odd modulus

Everything here is about a function `g : ℕ → ℤ` on the positive integers below `p`
(think `g = ε · λ`), with only the local dilation laws for 2, 3, 5 and ONE exclusion:
no pair `a + b = p` has `g a = g b = 1`.  Nothing about primality is used in this file.

Notation of the paper draft (ODD_CASE_PROOF_DRAFT.md), with ε absorbed into `g`:
* `A x  = g x - g (p - 2x)`   (the ×2 defect on `(p/4, p/2)`),
* `T1 x = g x - g (p - 3x)`   (the ×3 defect on `(p/6, p/3)`),
* `T2 x = g x + g (3x - p)`   (the ×3 defect on `(p/3, p/2)`).
-/

namespace OddCase

/-- One exclusion at `p`, with the local dilation laws for 2, 3 and 5. -/
structure OneExcl (p : ℕ) (g : ℕ → ℤ) : Prop where
  sign : ∀ n, 0 < n → n < p → g n = 1 ∨ g n = -1
  two : ∀ n, 0 < n → 2 * n < p → g (2 * n) = - g n
  three : ∀ n, 0 < n → 3 * n < p → g (3 * n) = - g n
  five : ∀ n, 0 < n → 5 * n < p → g (5 * n) = - g n
  noPP : ∀ a b, 0 < a → 0 < b → a + b = p → ¬ (g a = 1 ∧ g b = 1)

def A (p : ℕ) (g : ℕ → ℤ) (x : ℕ) : ℤ := g x - g (p - 2 * x)
def T1 (p : ℕ) (g : ℕ → ℤ) (x : ℕ) : ℤ := g x - g (p - 3 * x)
def T2 (p : ℕ) (g : ℕ → ℤ) (x : ℕ) : ℤ := g x + g (3 * x - p)

namespace OneExcl

variable {p : ℕ} {g : ℕ → ℤ} (H : OneExcl p g)
include H

/-! ### Lemma 1: the defects are nonnegative on the positive half -/

theorem A_nonneg {n : ℕ} (hlo : p < 4 * n) (hhi : 2 * n < p) : 0 ≤ A p g n := by
  unfold A
  have h2 := H.two n (by omega) hhi
  have h := H.noPP (2 * n) (p - 2 * n) (by omega) (by omega) (by omega)
  rcases H.sign n (by omega) (by omega) with h1 | h1 <;>
    rcases H.sign (p - 2 * n) (by omega) (by omega) with h3 | h3 <;> omega

theorem T1_nonneg {n : ℕ} (hlo : p < 6 * n) (hhi : 3 * n < p) : 0 ≤ T1 p g n := by
  unfold T1
  have h3 := H.three n (by omega) hhi
  have h := H.noPP (3 * n) (p - 3 * n) (by omega) (by omega) (by omega)
  rcases H.sign n (by omega) (by omega) with h1 | h1 <;>
    rcases H.sign (p - 3 * n) (by omega) (by omega) with h4 | h4 <;> omega

theorem T2_nonneg {n : ℕ} (hlo : p < 3 * n) (hhi : 2 * n < p) : 0 ≤ T2 p g n := by
  have hA := H.A_nonneg (n := n) (by omega) hhi
  unfold A at hA
  unfold T2
  have h3 := H.three (p - 2 * n) (by omega) (by omega)
  have h2 := H.two (3 * n - p) (by omega) (by omega)
  have h := H.noPP (3 * (p - 2 * n)) (2 * (3 * n - p)) (by omega) (by omega) (by omega)
  rcases H.sign n (by omega) (by omega) with h1 | h1 <;>
    rcases H.sign (p - 2 * n) (by omega) (by omega) with h4 | h4 <;>
    rcases H.sign (3 * n - p) (by omega) (by omega) with h5 | h5 <;> omega

/-! ### The commuting identity on the four ranges -/

theorem R1 {x : ℕ} (hx : 0 < x) (h6 : 6 * x < p) : A p g (3 * x) = T1 p g (2 * x) := by
  unfold A T1
  have e : p - 2 * (3 * x) = p - 3 * (2 * x) := by omega
  rw [e, H.three x hx (by omega), H.two x hx (by omega)]

theorem R2 {x : ℕ} (hlo : p < 6 * x) (hhi : 4 * x < p) :
    - A p g (p - 3 * x) = T1 p g x + T2 p g (2 * x) := by
  unfold A T1 T2
  have e : p - 2 * (p - 3 * x) = 3 * (2 * x) - p := by omega
  rw [e, H.two x (by omega) (by omega)]
  ring

theorem R3 {x : ℕ} (hlo : p < 4 * x) (hhi : 3 * x < p) :
    A p g x = T1 p g x - T2 p g (p - 2 * x) := by
  unfold A T1 T2
  have e : 3 * (p - 2 * x) - p = 2 * (p - 3 * x) := by omega
  rw [e, H.two (p - 3 * x) (by omega) (by omega)]
  ring

/-- R4 below `5p/12`: here `a(3x-p) = 0` and `t(p-2x) = T1 (p-2x)`. -/
theorem R4a {x : ℕ} (hlo : p < 3 * x) (hhi : 12 * x < 5 * p) :
    A p g x = T2 p g x - T1 p g (p - 2 * x) := by
  unfold A T1 T2
  have e : p - 3 * (p - 2 * x) = 2 * (3 * x - p) := by omega
  rw [e, H.two (3 * x - p) (by omega) (by omega)]
  ring

/-- R4 above `5p/12`: here `t(p-2x) = 0` and `a(3x-p) = A (3x-p)`. -/
theorem R4b {x : ℕ} (hlo : 5 * p < 12 * x) (hhi : 2 * x < p) :
    A p g (3 * x - p) + A p g x = T2 p g x := by
  unfold A T2
  have e : p - 2 * (3 * x - p) = 3 * (p - 2 * x) := by omega
  rw [e, H.three (p - 2 * x) (by omega) (by omega)]
  ring

/-! ### Consequences of R2 (both sides have opposite signs) -/

theorem R2_all {x : ℕ} (hlo : p < 6 * x) (hhi : 4 * x < p) :
    A p g (p - 3 * x) = 0 ∧ T1 p g x = 0 ∧ T2 p g (2 * x) = 0 := by
  have h := H.R2 hlo hhi
  have ha := H.A_nonneg (n := p - 3 * x) (by omega) (by omega)
  have ht1 := H.T1_nonneg (n := x) hlo (by omega)
  have ht2 := H.T2_nonneg (n := 2 * x) (by omega) (by omega)
  refine ⟨by linarith, by linarith, by linarith⟩

theorem T1_zero_low {x : ℕ} (hlo : p < 6 * x) (hhi : 4 * x < p) : T1 p g x = 0 :=
  (H.R2_all hlo hhi).2.1

theorem T2_zero_even {y : ℕ} (hlo : p < 3 * y) (hhi : 2 * y < p) (hy : y % 2 = 0) :
    T2 p g y = 0 := by
  have := (H.R2_all (x := y / 2) (by omega) (by omega)).2.2
  rwa [show 2 * (y / 2) = y by omega] at this

end OneExcl
end OddCase
