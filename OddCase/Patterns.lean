import OddCase.Main
import SignPatterns

set_option linter.unusedSimpArgs false

/-!
# Theorem C: all four Liouville sign patterns at every `N ≥ 2` outside `{2,3,4,5,6,9,10}`

(−,−) at even `N`: the background theorem `LiouvilleGoldbach.liouville_goldbach`.
(+,+) at even `N`: `SignPatterns.positivePair_even`.
(+,+), (−,−) at odd `N`: Theorem B at a prime factor `r ≥ 5`, scaled; powers of 3 via 27.
Mixed: Mangerel, IMRN 2024 (16), 11865–11877, Theorem 1.2 — taken as the explicit hypothesis
`SignPatterns.MangerelNonextremality`, not proved here.
-/

namespace OddCase

open LiouvilleGoldbach LiouvilleGoldbach.Final

/-- `N = a + b` with `λ(a) = s`, `λ(b) = t`. -/
def SignPair (N : ℕ) (s t : ℤ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = N ∧ liouville a = s ∧ liouville b = t

theorem SignPair.scale {N c : ℕ} {s t : ℤ} (h : SignPair N s t) (hc : 0 < c) :
    SignPair (c * N) (liouville c * s) (liouville c * t) := by
  obtain ⟨a, b, ha, hb, hab, h1, h2⟩ := h
  refine ⟨c * a, c * b, Nat.mul_pos hc ha, Nat.mul_pos hc hb, by rw [← mul_add, hab], ?_, ?_⟩
  · rw [ArithmeticFunction.liouville_apply_mul, h1]
  · rw [ArithmeticFunction.liouville_apply_mul, h2]

theorem liouville_sq_mul {c : ℕ} (hc : 0 < c) (e : ℤ) : liouville c * (liouville c * e) = e := by
  rcases liouville_sign hc with h | h <;> rw [h] <;> ring

theorem sign_mul {c : ℕ} (hc : 0 < c) {e : ℤ} (he : e = 1 ∨ e = -1) :
    liouville c * e = 1 ∨ liouville c * e = -1 := by
  rcases liouville_sign hc with h | h <;> rcases he with rfl | rfl <;> simp [h]

theorem equal_pair_27 {e : ℤ} (he : e = 1 ∨ e = -1) : SignPair 27 e e := by
  rcases he with rfl | rfl
  · refine ⟨1, 26, by omega, by omega, rfl, ArithmeticFunction.liouville_apply_one, ?_⟩
    rw [show (26 : ℕ) = 2 * 13 by norm_num, liouville_mul_prime Nat.prime_two,
      liouville_prime (by norm_num)]; norm_num
  · refine ⟨7, 20, by omega, by omega, rfl, liouville_prime (by norm_num), ?_⟩
    rw [show (20 : ℕ) = 2 * (2 * 5) by norm_num, liouville_mul_prime Nat.prime_two,
      liouville_mul_prime Nat.prime_two, liouville_prime (by norm_num)]; norm_num

/-- Both equal-sign patterns at every odd `N` other than 1, 3, 9. -/
theorem equal_pair_odd {N : ℕ} (hodd : N % 2 = 1) (h1 : N ≠ 1) (h3 : N ≠ 3) (h9 : N ≠ 9)
    {e : ℤ} (he : e = 1 ∨ e = -1) : SignPair N e e := by
  have hN0 : N ≠ 0 := by omega
  by_cases hr : ∃ r, r.Prime ∧ 5 ≤ r ∧ r ∣ N
  · obtain ⟨r, hr, hr5, c, rfl⟩ := hr
    have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hN0)
    obtain ⟨a, b, ha, hb, hab, ha', hb'⟩ := equal_pair_at_prime hr hr5 (sign_mul hc he)
    have hs := SignPair.scale ⟨a, b, ha, hb, hab, ha', hb'⟩ hc
    rw [liouville_sq_mul hc] at hs
    rwa [mul_comm] at hs
  · push_neg at hr
    have hpow : N = 3 ^ N.primeFactorsList.length := by
      apply Nat.eq_prime_pow_of_unique_prime_dvd hN0
      intro d hd hdN
      by_contra hne
      have hd2 : d ≠ 2 := by
        rintro rfl
        omega
      have h5 : 5 ≤ d := by
        have := hd.two_le
        by_contra hlt
        have h4 : d = 4 := by omega
        subst h4
        exact absurd hd (by decide)
      exact hr d hd h5 hdN
    obtain ⟨k, hk⟩ : ∃ k, N = 3 ^ k := ⟨_, hpow⟩
    clear hpow hr
    have hk3 : 3 ≤ k := by
      by_contra hlt
      interval_cases k <;> norm_num at hk <;> omega
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hN' : N = 3 ^ j * 27 := by rw [hk, pow_add]; norm_num
    have hc : 0 < 3 ^ j := by positivity
    have hs := SignPair.scale (equal_pair_27 (sign_mul hc he)) hc
    rw [liouville_sq_mul hc] at hs
    rw [hN']; exact hs

/-- **Theorem C.** Given Mangerel's nonextremality theorem, every `N ≥ 2` outside
`{2, 3, 4, 5, 6, 9, 10}` exhibits all four sign patterns `(λ(a), λ(N - a))`. -/
theorem all_four_patterns (H : SignPatterns.MangerelNonextremality) {N : ℕ} (hN : 2 ≤ N)
    (h2 : N ≠ 2) (h3 : N ≠ 3) (h4 : N ≠ 4) (h5 : N ≠ 5) (h6 : N ≠ 6) (h9 : N ≠ 9)
    (h10 : N ≠ 10) {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    SignPair N s t := by
  by_cases hst : s = t
  · subst hst
    by_cases hev : N % 2 = 0
    · rcases hs with rfl | rfl
      · obtain ⟨a, b, ha, hb, hab, h1, h2⟩ :=
          SignPatterns.positivePair_even N ⟨N / 2, by omega⟩ (by omega) h4 h6
        exact ⟨a, b, ha, hb, hab, h1, h2⟩
      · obtain ⟨a, b, ha, hb, hab, h1, h2⟩ := liouville_goldbach N ⟨N / 2, by omega⟩ (by omega)
        exact ⟨a, b, ha, hb, hab, h1, h2⟩
    · exact equal_pair_odd (by omega) (by omega) h3 h9 hs
  · have hmix : SignPatterns.MixedPair N := by
      by_cases h11 : 11 ≤ N
      · exact SignPatterns.mixedPair_of_nonextremality H h11
      · have : N = 7 ∨ N = 8 := by omega
        rcases this with rfl | rfl
        · exact ⟨4, 3, by omega, by omega, rfl, liouville_small (Or.inl rfl),
            liouville_prime Nat.prime_three⟩
        · exact SignPatterns.mixedPair_eight
    obtain ⟨a, b, ha, hb, hab, h1, h2⟩ := hmix
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact absurd rfl hst
    · exact ⟨a, b, ha, hb, hab, h1, h2⟩
    · exact ⟨b, a, hb, ha, by omega, h2, h1⟩
    · exact absurd rfl hst

/-! ### The seven exceptions are sharp -/

section Sharp
open SignPatterns

theorem not_pair_two : ¬ SignPair 2 (-1) (-1) := by
  rintro ⟨a, b, ha, hb, hab, h1, h2⟩
  obtain rfl : a = 1 := by omega
  simp [ArithmeticFunction.liouville_apply_one] at h1

theorem not_pair_three (e : ℤ) : ¬ SignPair 3 e e := by
  rintro ⟨a, b, ha, hb, hab, h1, h2⟩
  have l1 : liouville 1 = 1 := ArithmeticFunction.liouville_apply_one
  have l2 := SignPatterns.liouville_two
  have ha3 : a < 3 := by omega
  obtain rfl : b = 3 - a := by omega
  interval_cases a <;> simp_all

theorem not_pp_four : ¬ SignPair 4 1 1 := by
  rintro ⟨a, b, ha, hb, hab, h1, h2⟩
  exact SignPatterns.not_positivePair_four ⟨a, b, ha, hb, hab, h1, h2⟩

theorem not_mixed_five : ¬ SignPair 5 1 (-1) := by
  rintro ⟨a, b, ha, hb, hab, h1, h2⟩
  have l1 : liouville 1 = 1 := ArithmeticFunction.liouville_apply_one
  have l2 := SignPatterns.liouville_two; have l3 := SignPatterns.liouville_three
  have l4 := SignPatterns.liouville_four
  have ha5 : a < 5 := by omega
  obtain rfl : b = 5 - a := by omega
  interval_cases a <;> simp_all

theorem not_pp_six : ¬ SignPair 6 1 1 := by
  rintro ⟨a, b, ha, hb, hab, h1, h2⟩
  exact SignPatterns.not_positivePair_six ⟨a, b, ha, hb, hab, h1, h2⟩

theorem not_pp_nine : ¬ SignPair 9 1 1 := by
  rintro ⟨a, b, ha, hb, hab, h1, h2⟩
  have l1 : liouville 1 = 1 := ArithmeticFunction.liouville_apply_one
  have l2 := SignPatterns.liouville_two; have l3 := SignPatterns.liouville_three
  have l4 := SignPatterns.liouville_four; have l5 := SignPatterns.liouville_five
  have l6 := SignPatterns.liouville_six; have l7 := SignPatterns.liouville_seven
  have l8 := SignPatterns.liouville_eight
  have ha9 : a < 9 := by omega
  obtain rfl : b = 9 - a := by omega
  interval_cases a <;> simp_all

theorem not_mixed_ten : ¬ SignPair 10 1 (-1) := by
  rintro ⟨a, b, ha, hb, hab, h1, h2⟩
  exact SignPatterns.not_mixedPair_ten ⟨a, b, ha, hb, hab, h1, h2⟩

end Sharp

end OddCase
