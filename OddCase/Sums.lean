import OddCase.Core

set_option linter.unusedSimpArgs false

/-!
# Lemma 3: the support of the ×2 defect (the summation argument)
-/

namespace OddCase
namespace OneExcl

variable {p : ℕ} {g : ℕ → ℤ} (H : OneExcl p g)

/-- Integers of `(p/4, p/3)`. -/
def Q (p : ℕ) : Finset ℕ := (Finset.range p).filter (fun x => p < 4 * x ∧ 3 * x < p)
/-- Integers of `(p/3, p/2)`. -/
def R (p : ℕ) : Finset ℕ := (Finset.range p).filter (fun x => p < 3 * x ∧ 2 * x < p)
/-- Integers of `(p/8, p/6)`. -/
def X (p : ℕ) : Finset ℕ := (Finset.range p).filter (fun x => p < 8 * x ∧ 6 * x < p)
/-- Multiples of 3 in `(3p/8, p/2)`. -/
def S (p : ℕ) : Finset ℕ := (R p).filter (fun y => 3 * p < 8 * y ∧ y % 3 = 0)
/-- Odd integers of `(p/6, p/3)`. -/
def Q' (p : ℕ) : Finset ℕ :=
  (Finset.range p).filter (fun z => p < 6 * z ∧ 3 * z < p ∧ z % 2 = 1)

include H

variable (hp2 : p % 2 = 1)
include hp2

theorem sum_identity :
    ∑ x ∈ Q p, A p g x
      + ∑ x ∈ (R p).filter (fun y => ¬ (3 * p < 8 * y ∧ y % 3 = 0)), A p g x
      + ∑ x ∈ (R p).filter (fun x => 5 * p < 12 * x), A p g (3 * x - p) = 0 := by
  classical
  -- (1) R3 summed over Q, and reindexing its last sum onto the odd part of R
  have h1 : ∑ x ∈ Q p, A p g x = ∑ x ∈ Q p, T1 p g x - ∑ x ∈ Q p, T2 p g (p - 2 * x) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hx
    exact H.R3 hx.2.1 hx.2.2
  have h2 : ∑ x ∈ Q p, T2 p g (p - 2 * x) = ∑ y ∈ (R p).filter (fun y => y % 2 = 1), T2 p g y := by
    refine Finset.sum_nbij' (fun x => p - 2 * x) (fun y => (p - y) / 2) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hx ⊢
      omega
    · intro y hy
      simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hy ⊢
      omega
    · intro x hx
      simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hx
      omega
    · intro y hy
      simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hy
      omega
    · intro x _; rfl
  -- (3) split R at 5p/12
  have hsplitR : ∀ F : ℕ → ℤ, ∑ x ∈ R p, F x =
      ∑ x ∈ (R p).filter (fun x => 12 * x < 5 * p), F x
        + ∑ x ∈ (R p).filter (fun x => 5 * p < 12 * x), F x := by
    intro F
    rw [← Finset.sum_filter_add_sum_filter_not (R p) (fun x => 12 * x < 5 * p)]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext x
    simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range]
    omega
  have h3a : ∑ x ∈ (R p).filter (fun x => 12 * x < 5 * p), A p g x =
      ∑ x ∈ (R p).filter (fun x => 12 * x < 5 * p), T2 p g x
        - ∑ x ∈ (R p).filter (fun x => 12 * x < 5 * p), T1 p g (p - 2 * x) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hx
    exact H.R4a hx.1.2.1 hx.2
  have h3b : ∑ x ∈ (R p).filter (fun x => 5 * p < 12 * x), (A p g (3 * x - p) + A p g x) =
      ∑ x ∈ (R p).filter (fun x => 5 * p < 12 * x), T2 p g x := by
    refine Finset.sum_congr rfl (fun x hx => ?_)
    simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hx
    exact H.R4b hx.2 hx.1.2.2
  -- (4) reindex the T1 sum over the lower part of R onto Q', then drop (p/6, p/4)
  have h4 : ∑ x ∈ (R p).filter (fun x => 12 * x < 5 * p), T1 p g (p - 2 * x) =
      ∑ z ∈ (Q p).filter (fun z => z % 2 = 1), T1 p g z := by
    have e1 : ∑ x ∈ (R p).filter (fun x => 12 * x < 5 * p), T1 p g (p - 2 * x) =
        ∑ z ∈ Q' p, T1 p g z := by
      refine Finset.sum_nbij' (fun x => p - 2 * x) (fun z => (p - z) / 2) ?_ ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hx ⊢
        omega
      · intro z hz
        simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hz ⊢
        omega
      · intro x hx
        simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hx
        omega
      · intro z hz
        simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hz
        omega
      · intro x _; rfl
    rw [e1, ← Finset.sum_filter_add_sum_filter_not (Q' p) (fun z => p < 4 * z)]
    have e2 : ∑ z ∈ (Q' p).filter (fun z => ¬ p < 4 * z), T1 p g z = 0 := by
      refine Finset.sum_eq_zero (fun z hz => ?_)
      simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hz
      exact H.T1_zero_low (by omega) (by omega)
    rw [e2, add_zero]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext z
    simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range]
    omega
  -- (5) the even part of R carries no T2
  have h5 : ∑ y ∈ R p, T2 p g y = ∑ y ∈ (R p).filter (fun y => y % 2 = 1), T2 p g y := by
    rw [← Finset.sum_filter_add_sum_filter_not (R p) (fun y => y % 2 = 1)]
    have : ∑ y ∈ (R p).filter (fun y => ¬ y % 2 = 1), T2 p g y = 0 := by
      refine Finset.sum_eq_zero (fun y hy => ?_)
      simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hy
      exact H.T2_zero_even hy.1.2.1 hy.1.2.2 (by omega)
    rw [this, add_zero]
  -- (6),(7) the even part of Q carries sum_S A
  have h6 : ∑ z ∈ Q p, T1 p g z = ∑ z ∈ (Q p).filter (fun z => z % 2 = 1), T1 p g z
      + ∑ y ∈ S p, A p g y := by
    rw [← Finset.sum_filter_add_sum_filter_not (Q p) (fun z => z % 2 = 1)]
    congr 1
    have e1 : ∑ z ∈ (Q p).filter (fun z => ¬ z % 2 = 1), T1 p g z = ∑ x ∈ X p, T1 p g (2 * x) := by
      refine Finset.sum_nbij' (fun z => z / 2) (fun x => 2 * x) ?_ ?_ ?_ ?_ ?_
      · intro z hz
        simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hz ⊢
        omega
      · intro x hx
        simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hx ⊢
        omega
      · intro z hz
        simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hz
        omega
      · intro x _; omega
      · intro z hz
        simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hz
        congr 1; omega
    have e2 : ∑ x ∈ X p, T1 p g (2 * x) = ∑ x ∈ X p, A p g (3 * x) := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hx
      exact (H.R1 (by omega) hx.2.2).symm
    have e3 : ∑ x ∈ X p, A p g (3 * x) = ∑ y ∈ S p, A p g y := by
      refine Finset.sum_nbij' (fun x => 3 * x) (fun y => y / 3) ?_ ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hx ⊢
        omega
      · intro y hy
        simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hy ⊢
        omega
      · intro x _; omega
      · intro y hy
        simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hy
        omega
      · intro x _; rfl
    rw [e1, e2, e3]
  -- (8) split sum_R A into S and the rest
  have h8 : ∑ y ∈ R p, A p g y = ∑ y ∈ S p, A p g y
      + ∑ x ∈ (R p).filter (fun y => ¬ (3 * p < 8 * y ∧ y % 3 = 0)), A p g x := by
    rw [← Finset.sum_filter_add_sum_filter_not (R p) (fun y => 3 * p < 8 * y ∧ y % 3 = 0)]
    rfl
  -- combine
  have hRA := hsplitR (A p g)
  have hRT := hsplitR (T2 p g)
  rw [Finset.sum_add_distrib] at h3b
  linarith [h1, h2, h3a, h3b, h4, h5, h6, h8, hRA, hRT]

/-- Lemma 3: the ×2 defect vanishes on `(p/4, p/2)` except possibly at multiples of 3 above `3p/8`,
and `a(3x - p) = 0` for `x` in `(5p/12, p/2)`. -/
theorem support
    : (∀ x ∈ Q p, A p g x = 0)
      ∧ (∀ x ∈ (R p).filter (fun y => ¬ (3 * p < 8 * y ∧ y % 3 = 0)), A p g x = 0)
      ∧ (∀ x ∈ (R p).filter (fun x => 5 * p < 12 * x), A p g (3 * x - p) = 0) := by
  classical
  have hs := H.sum_identity hp2
  have n1 : ∀ x ∈ Q p, 0 ≤ A p g x := by
    intro x hx
    simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hx
    exact H.A_nonneg hx.2.1 (by omega)
  have n2 : ∀ x ∈ (R p).filter (fun y => ¬ (3 * p < 8 * y ∧ y % 3 = 0)), 0 ≤ A p g x := by
    intro x hx
    simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hx
    exact H.A_nonneg (by omega) hx.1.2.2
  have n3 : ∀ x ∈ (R p).filter (fun x => 5 * p < 12 * x), 0 ≤ A p g (3 * x - p) := by
    intro x hx
    simp only [Q, R, X, S, Q', Finset.mem_filter, Finset.mem_range] at hx
    exact H.A_nonneg (by omega) (by omega)
  have s1 := Finset.sum_nonneg n1
  have s2 := Finset.sum_nonneg n2
  have s3 := Finset.sum_nonneg n3
  refine ⟨?_, ?_, ?_⟩
  · exact (Finset.sum_eq_zero_iff_of_nonneg n1).mp (by linarith)
  · exact (Finset.sum_eq_zero_iff_of_nonneg n2).mp (by linarith)
  · exact (Finset.sum_eq_zero_iff_of_nonneg n3).mp (by linarith)

end OneExcl
end OddCase
