import OddCase.Sums

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-!
# The map Phi, the cycle lemma (Lemma 5), and the exact laws
-/

namespace OddCase
namespace OneExcl

variable {p : ℕ} {g : ℕ → ℤ} (H : OneExcl p g) (hp2 : p % 2 = 1)
include H hp2

/-- Above `3p/8` the ×3 defect equals the ×2 defect. -/
theorem T2_eq_A_upper {y : ℕ} (hlo : 3 * p < 8 * y) (hhi : 2 * y < p) :
    T2 p g y = A p g y := by
  have hs := H.support hp2
  by_cases h12 : 12 * y < 5 * p
  · have h := H.R4a (x := y) (by omega) h12
    have hz := H.T1_zero_low (x := p - 2 * y) (by omega) (by omega)
    linarith
  · have h := H.R4b (x := y) (by omega) hhi
    have hz := hs.2.2 y (by simp only [R, Finset.mem_filter, Finset.mem_range]; omega)
    linarith

/-- Phi, lower branch: `t(y) = t(4y - p)`. -/
theorem phi_step {y : ℕ} (hlo : p < 3 * y) (h8 : 8 * y < 3 * p) :
    T2 p g y = T2 p g (4 * y - p) := by
  have hs := H.support hp2
  have hA : A p g y = 0 :=
    hs.2.1 y (by simp only [R, Finset.mem_filter, Finset.mem_range]; omega)
  have h4a := H.R4a (x := y) hlo (by omega)
  have hAz : A p g (p - 2 * y) = 0 :=
    hs.1 (p - 2 * y) (by simp only [Q, Finset.mem_filter, Finset.mem_range]; omega)
  have h3 := H.R3 (x := p - 2 * y) (by omega) (by omega)
  have e : p - 2 * (p - 2 * y) = 4 * y - p := by omega
  rw [e] at h3
  linarith

/-- Phi, upper branch at a multiple of 3: `t(3k) = t(p - 4k)`. -/
theorem psi_step {k : ℕ} (hlo : 3 * p < 8 * (3 * k)) (hhi : 2 * (3 * k) < p) :
    T2 p g (3 * k) = T2 p g (p - 4 * k) := by
  have hs := H.support hp2
  have h1 := H.T2_eq_A_upper hp2 hlo hhi
  have hR1 := H.R1 (x := k) (by omega) (by omega)
  have hA2 : A p g (2 * k) = 0 :=
    hs.1 (2 * k) (by simp only [Q, Finset.mem_filter, Finset.mem_range]; omega)
  have h3 := H.R3 (x := 2 * k) (by omega) (by omega)
  have e : p - 2 * (2 * k) = p - 4 * k := by omega
  rw [e] at h3
  linarith

/-- Terminal vertices: above `3p/8` and not a multiple of 3. -/
theorem terminal {y : ℕ} (hlo : 3 * p < 8 * y) (hhi : 2 * y < p) (h3 : y % 3 ≠ 0) :
    T2 p g y = 0 := by
  have hs := H.support hp2
  rw [H.T2_eq_A_upper hp2 hlo hhi]
  exact hs.2.1 y (by simp only [R, Finset.mem_filter, Finset.mem_range]; omega)

omit hp2 in
/-- Lemma 5 (uses the ×5 law): no defect at a lower-branch point `y ≡ p (mod 4)`. -/
theorem template {y : ℕ} (hlo : p < 3 * y) (h8 : 8 * y < 3 * p) (hodd : y % 2 = 1)
    (hp2 : p % 2 = 1) (h4 : y % 4 = p % 4) : T2 p g y = 0 := by
  have hnn := H.T2_nonneg (n := y) hlo (by omega)
  unfold T2 at hnn ⊢
  -- names: w = (3y-p)/2, s = (p-y)/2, h = s/2, z = (5y-p)/4, k = (p-5w)/2
  by_contra hne
  have hy : g y = 1 := by
    rcases H.sign y (by omega) (by omega) with h | h <;>
      rcases H.sign (3 * y - p) (by omega) (by omega) with h' | h' <;> omega
  have hv : g (3 * y - p) = 1 := by
    rcases H.sign y (by omega) (by omega) with h | h <;>
      rcases H.sign (3 * y - p) (by omega) (by omega) with h' | h' <;> omega
  -- g w = -1
  have ew : 3 * y - p = 2 * ((3 * y - p) / 2) := by omega
  have hw : g ((3 * y - p) / 2) = -1 := by
    have := H.two ((3 * y - p) / 2) (by omega) (by omega)
    rw [← ew, hv] at this; linarith
  -- chain 1: pair (2s, y), then s = 2h, then pair (5h, z)
  have es : p - y = 2 * ((p - y) / 2) := by omega
  have h2s : g (p - y) = -1 := by
    have hx := H.noPP (p - y) y (by omega) (by omega) (by omega)
    rcases H.sign (p - y) (by omega) (by omega) with h | h
    · exact absurd ⟨h, hy⟩ hx
    · exact h
  have hs : g ((p - y) / 2) = 1 := by
    have := H.two ((p - y) / 2) (by omega) (by omega)
    rw [← es, h2s] at this; linarith
  have eh : (p - y) / 2 = 2 * ((p - y) / 4) := by omega
  have hh : g ((p - y) / 4) = -1 := by
    have := H.two ((p - y) / 4) (by omega) (by omega)
    rw [← eh, hs] at this; linarith
  have h5h : g (5 * ((p - y) / 4)) = 1 := by
    have := H.five ((p - y) / 4) (by omega) (by omega)
    rw [hh] at this; linarith
  have hz1 : g ((5 * y - p) / 4) = -1 := by
    have hx := H.noPP (5 * ((p - y) / 4)) ((5 * y - p) / 4) (by omega) (by omega) (by omega)
    rcases H.sign ((5 * y - p) / 4) (by omega) (by omega) with h | h
    · exact absurd ⟨h5h, h⟩ hx
    · exact h
  -- chain 2: g(5w) = 1, pair (2k, 5w), pair (3z, k)
  have h5w : g (5 * ((3 * y - p) / 2)) = 1 := by
    have := H.five ((3 * y - p) / 2) (by omega) (by omega)
    rw [hw] at this; linarith
  have ek : p - 5 * ((3 * y - p) / 2) = 2 * ((p - 5 * ((3 * y - p) / 2)) / 2) := by omega
  have h2k : g (p - 5 * ((3 * y - p) / 2)) = -1 := by
    have hx := H.noPP (p - 5 * ((3 * y - p) / 2)) (5 * ((3 * y - p) / 2))
      (by omega) (by omega) (by omega)
    rcases H.sign (p - 5 * ((3 * y - p) / 2)) (by omega) (by omega) with h | h
    · exact absurd ⟨h, h5w⟩ hx
    · exact h
  have hk : g ((p - 5 * ((3 * y - p) / 2)) / 2) = 1 := by
    have := H.two ((p - 5 * ((3 * y - p) / 2)) / 2) (by omega) (by omega)
    rw [← ek, h2k] at this; linarith
  have h3z : g (3 * ((5 * y - p) / 4)) = -1 := by
    have hx := H.noPP (3 * ((5 * y - p) / 4)) ((p - 5 * ((3 * y - p) / 2)) / 2)
      (by omega) (by omega) (by omega)
    rcases H.sign (3 * ((5 * y - p) / 4)) (by omega) (by omega) with h | h
    · exact absurd ⟨h, hk⟩ hx
    · exact h
  have hz2 : g ((5 * y - p) / 4) = 1 := by
    have := H.three ((5 * y - p) / 4) (by omega) (by omega)
    rw [h3z] at this; linarith
  rw [hz1] at hz2; norm_num at hz2

/-- The well-founded measure: lower-branch points sit above every upper-branch point. -/
def mu (p y : ℕ) : ℕ :=
  if 8 * y < 3 * p then 2 * p - y
  else if 3 * p ≤ 7 * y then p - (7 * y - 3 * p) else p - (3 * p - 7 * y)

theorem T2_zero_odd (hp7 : p % 7 ≠ 0) :
    ∀ y, p < 3 * y → 2 * y < p → y % 2 = 1 → T2 p g y = 0 := by
  suffices key : ∀ m y, mu p y ≤ m → p < 3 * y → 2 * y < p → y % 2 = 1 → T2 p g y = 0 by
    intro y h1 h2 h3; exact key _ y le_rfl h1 h2 h3
  intro m
  induction m with
  | zero =>
    intro y hm h1 h2 h3
    unfold mu at hm
    split_ifs at hm <;> omega
  | succ m ih =>
    intro y hm h1 h2 h3
    by_cases h8 : 8 * y < 3 * p
    · -- lower branch
      by_cases h4 : y % 4 = p % 4
      · exact H.template h1 h8 h3 hp2 h4
      · rw [H.phi_step hp2 h1 h8]
        apply ih (4 * y - p) _ (by omega) (by omega) (by omega)
        unfold mu at hm ⊢
        split_ifs at hm ⊢ <;> omega
    · -- upper branch
      have h8' : 3 * p < 8 * y := by omega
      by_cases h3y : y % 3 = 0
      · obtain ⟨k, rfl⟩ : ∃ k, y = 3 * k := ⟨y / 3, by omega⟩
        rw [H.psi_step hp2 h8' h2]
        by_cases hn8 : 8 * (p - 4 * k) < 3 * p
        · exact H.template (by omega) hn8 (by omega) hp2 (by omega)
        · have hk : 7 * k ≠ p := by omega
          apply ih (p - 4 * k) _ (by omega) (by omega) (by omega)
          unfold mu at hm ⊢
          split_ifs at hm ⊢ <;> omega
      · exact H.terminal hp2 h8' h2 h3y

/-- Theorem A, at every modulus: the two exact band identities. -/
theorem exact_bands (hp3 : p % 3 ≠ 0) (hp7 : p % 7 ≠ 0) :
    (∀ n, p < 4 * n → 2 * n < p → g (p - 2 * n) = g n) ∧
    (∀ n, p < 3 * n → 2 * n < p → g (3 * n - p) = - g n) := by
  have hs := H.support hp2
  have hT2 : ∀ n, p < 3 * n → 2 * n < p → T2 p g n = 0 := by
    intro n h1 h2
    by_cases hodd : n % 2 = 1
    · exact H.T2_zero_odd hp2 hp7 n h1 h2 hodd
    · exact H.T2_zero_even h1 h2 (by omega)
  refine ⟨fun n h1 h2 => ?_, fun n h1 h2 => ?_⟩
  · have hA : A p g n = 0 := by
      by_cases hq : 3 * n < p
      · exact hs.1 n (by simp only [Q, Finset.mem_filter, Finset.mem_range]; omega)
      have hr : p < 3 * n := by omega
      by_cases hS : 3 * p < 8 * n ∧ n % 3 = 0
      · rw [← H.T2_eq_A_upper hp2 hS.1 h2]; exact hT2 n hr h2
      · exact hs.2.1 n (by simp only [R, Finset.mem_filter, Finset.mem_range]; omega)
    unfold A at hA; linarith
  · have := hT2 n h1 h2
    unfold T2 at this; linarith

end OneExcl
end OddCase
