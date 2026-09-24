import LiouvilleGoldbach

/-!
# All four Liouville sign patterns at even totals

Corollaries of `LiouvilleGoldbach.positive_prime_pairs` and
`LiouvilleGoldbach.liouville_goldbach`.

* `positivePair_even`: every even `N ∉ {4, 6}` is `a + b` with `λ(a) = λ(b) = 1`.
  Unconditional.
* `mixedPair_of_nonextremality`: every `N ≥ 11` is `a + b` with `λ(a) = 1`,
  `λ(b) = -1`, assuming Mangerel's nonextremality theorem
  (IMRN 2024, Theorem 1.2), stated exactly as in the multiples-of-four repository.
* `all_patterns_even`: every even `N ∉ {2, 4, 6, 10}` shows all four patterns.
* The exceptions are sharp: `not_negativePair_two`, `not_positivePair_four`,
  `not_positivePair_six`, `not_mixedPair_two`, `not_mixedPair_ten`.
-/

namespace SignPatterns

open LiouvilleGoldbach LiouvilleGoldbach.Final

def PositivePair (N : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = N ∧ liouville a = 1 ∧ liouville b = 1

def MixedPair (N : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = N ∧ liouville a = 1 ∧ liouville b = -1

/-- Mangerel, IMRN 2024, Theorem 1.2 (taken as a hypothesis, not proved here). -/
def MangerelNonextremality : Prop :=
  ∀ m : ℕ, 11 ≤ m →
    |∑ n ∈ Finset.Icc 1 (m - 1), liouville n * liouville (m - n)| < (m : ℤ) - 1

/-- Scaling a negative-negative pair by a factor of sign `-1` gives a
positive-positive pair. -/
theorem NegativePair.scale_neg {N r : ℕ} (h : NegativePair N)
    (hr : 0 < r) (hlam : liouville r = -1) : PositivePair (r * N) := by
  rcases h with ⟨a, b, ha, hb, hab, hlama, hlamb⟩
  refine ⟨r * a, r * b, Nat.mul_pos hr ha, Nat.mul_pos hr hb, ?_, ?_, ?_⟩
  · rw [← mul_add, hab]
  · rw [ArithmeticFunction.liouville_apply_mul, hlam, hlama]; norm_num
  · rw [ArithmeticFunction.liouville_apply_mul, hlam, hlamb]; norm_num

/-- Every even `N` other than `4` and `6` is a sum of two positive integers
with Liouville value `1`. For `N = 2m`: `m = 1` gives `1 + 1`; a prime `m > 3`
is `positive_prime_pairs`; a composite `m = r k` scales the negative-negative
pair at `2k` by the prime `r`. -/
theorem positivePair_even (N : ℕ) (hEven : Even N) (hN : 0 < N)
    (h4 : N ≠ 4) (h6 : N ≠ 6) : PositivePair N := by
  rcases hEven with ⟨m, rfl⟩
  by_cases hm1 : m = 1
  · subst hm1
    exact ⟨1, 1, by omega, by omega, rfl,
      ArithmeticFunction.liouville_apply_one, ArithmeticFunction.liouville_apply_one⟩
  have hm : 1 < m := by omega
  by_cases hmp : m.Prime
  · have hm3 : 3 < m := by have := hmp.two_le; omega
    obtain ⟨a, b, ha, hb, hab, hla, hlb⟩ := positive_prime_pairs m hmp hm3
    exact ⟨a, b, ha, hb, by omega, hla, hlb⟩
  · obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    rcases hrdvd with ⟨k, rfl⟩
    have hk : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · interval_cases k <;> simp_all
      · exact h
    have hneg : NegativePair (2 * k) :=
      liouville_goldbach (2 * k) (even_two_mul k) (by omega)
    have hpos := NegativePair.scale_neg hneg hr.pos (liouville_prime hr)
    convert hpos using 1
    ring

/-- Mangerel's nonextremality forbids all pairs at `N ≥ 11` from having equal
signs, so a mixed pair exists. -/
theorem mixedPair_of_nonextremality (H : MangerelNonextremality)
    {N : ℕ} (hN : 11 ≤ N) : MixedPair N := by
  by_contra hnone
  have hprod : ∀ n ∈ Finset.Icc 1 (N - 1),
      liouville n * liouville (N - n) = 1 := by
    intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hn1, hnm⟩
    have hnpos : 0 < n := by omega
    have hmnp : 0 < N - n := by omega
    rcases liouville_sign hnpos with ha | ha <;>
      rcases liouville_sign hmnp with hb | hb
    · rw [ha, hb]; norm_num
    · exact (hnone ⟨n, N - n, hnpos, hmnp, by omega, ha, hb⟩).elim
    · exact (hnone ⟨N - n, n, hmnp, hnpos, by omega, hb, ha⟩).elim
    · rw [ha, hb]; norm_num
  have hsum :
      (∑ n ∈ Finset.Icc 1 (N - 1), liouville n * liouville (N - n)) =
        (N : ℤ) - 1 := by
    calc
      _ = ∑ _n ∈ Finset.Icc 1 (N - 1), (1 : ℤ) :=
        Finset.sum_congr rfl hprod
      _ = (N : ℤ) - 1 := by
        simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
        have hcard : N - 1 + 1 - 1 = N - 1 := by omega
        rw [hcard, Nat.cast_sub (by omega : 1 ≤ N)]
        norm_num
  have hbound := H N hN
  rw [hsum, abs_of_nonneg (by omega : (0 : ℤ) ≤ N - 1)] at hbound
  exact (lt_irrefl _) hbound

theorem mixedPair_eight : MixedPair 8 :=
  ⟨1, 7, by omega, by omega, by omega, ArithmeticFunction.liouville_apply_one,
    liouville_prime (by decide)⟩

/-- Every even `N` outside `{2, 4, 6, 10}` exhibits all four sign patterns
`(λ(a), λ(N - a))`. Only the mixed patterns use Mangerel's theorem. -/
theorem all_patterns_even (H : MangerelNonextremality) (N : ℕ) (hEven : Even N)
    (hN : 2 < N) (h4 : N ≠ 4) (h6 : N ≠ 6) (h10 : N ≠ 10) :
    NegativePair N ∧ PositivePair N ∧ MixedPair N ∧
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = N ∧ liouville a = -1 ∧ liouville b = 1 := by
  have hmix : MixedPair N := by
    rcases Nat.lt_or_ge N 11 with h | h
    · obtain ⟨m, hm⟩ := hEven
      have h8 : N = 8 := by omega
      exact h8 ▸ mixedPair_eight
    · exact mixedPair_of_nonextremality H h
  refine ⟨liouville_goldbach N hEven hN,
    positivePair_even N hEven (by omega) h4 h6, hmix, ?_⟩
  obtain ⟨a, b, ha, hb, hab, hla, hlb⟩ := hmix
  exact ⟨b, a, hb, ha, by omega, hlb, hla⟩

/-! ### The exceptions are sharp -/

theorem liouville_two : liouville 2 = -1 := liouville_prime Nat.prime_two
theorem liouville_three : liouville 3 = -1 := liouville_prime Nat.prime_three
theorem liouville_five : liouville 5 = -1 := liouville_prime (by decide)
theorem liouville_seven : liouville 7 = -1 := liouville_prime (by decide)

theorem liouville_four : liouville 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, ArithmeticFunction.liouville_apply_mul,
    liouville_two]; norm_num
theorem liouville_six : liouville 6 = 1 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, ArithmeticFunction.liouville_apply_mul,
    liouville_two, liouville_three]; norm_num
theorem liouville_eight : liouville 8 = -1 := by
  rw [show (8 : ℕ) = 2 * 4 by norm_num, ArithmeticFunction.liouville_apply_mul,
    liouville_two, liouville_four]; norm_num
theorem liouville_nine : liouville 9 = 1 := by
  rw [show (9 : ℕ) = 3 * 3 by norm_num, ArithmeticFunction.liouville_apply_mul,
    liouville_three]; norm_num

theorem not_negativePair_two : ¬ NegativePair 2 := by
  rintro ⟨a, b, ha, hb, hab, hla, hlb⟩
  obtain rfl : a = 1 := by omega
  simp [ArithmeticFunction.liouville_apply_one] at hla

theorem not_mixedPair_two : ¬ MixedPair 2 := by
  rintro ⟨a, b, ha, hb, hab, hla, hlb⟩
  obtain rfl : b = 1 := by omega
  simp [ArithmeticFunction.liouville_apply_one] at hlb

theorem not_positivePair_four : ¬ PositivePair 4 := by
  rintro ⟨a, b, ha, hb, hab, hla, hlb⟩
  have ha4 : a < 4 := by omega
  obtain rfl : b = 4 - a := by omega
  have l2 := liouville_two; have l3 := liouville_three
  interval_cases a <;> simp_all

theorem not_positivePair_six : ¬ PositivePair 6 := by
  rintro ⟨a, b, ha, hb, hab, hla, hlb⟩
  have ha6 : a < 6 := by omega
  obtain rfl : b = 6 - a := by omega
  have l2 := liouville_two; have l3 := liouville_three; have l5 := liouville_five
  interval_cases a <;> simp_all

theorem not_mixedPair_ten : ¬ MixedPair 10 := by
  rintro ⟨a, b, ha, hb, hab, hla, hlb⟩
  have ha10 : a < 10 := by omega
  obtain rfl : b = 10 - a := by omega
  have l1 : liouville 1 = 1 := ArithmeticFunction.liouville_apply_one
  have l2 := liouville_two; have l3 := liouville_three; have l4 := liouville_four
  have l5 := liouville_five; have l6 := liouville_six; have l7 := liouville_seven
  have l8 := liouville_eight; have l9 := liouville_nine
  interval_cases a <;> simp_all

end SignPatterns
