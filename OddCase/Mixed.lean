import OddCase.Patterns

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-!
# Mixed patterns without Mangerel: `N ≥ 11` is never "all pairs equal"

If every pair `a + (N - a)` has `λ(a) = λ(N - a)`, the same holds at every divisor of `N`.
At a prime `p ≥ 7` this exact reflection symmetry makes the EVEN completion `G(x) = λ(|x|)`
exactly multiplicative by `-1, 2, 3`; the background extension lemma then makes `G`
multiplicative, and a prime quadratic residue `ℓ < p/2` gives `1 = G(ℓ) = λ(ℓ) = -1`.
As a corollary we prove Mangerel's nonextremality theorem (IMRN 2024, Thm 1.2) for `N ≥ 11`,
and Theorem C becomes unconditional.
-/

namespace OddCase

open LiouvilleGoldbach LiouvilleGoldbach.Final

/-- Every pair at `N` has equal Liouville signs. -/
def AllEqual (N : ℕ) : Prop := ∀ a, 0 < a → a < N → liouville (N - a) = liouville a

theorem AllEqual.of_dvd {d c : ℕ} (h : AllEqual (d * c)) (hc : 0 < c) : AllEqual d := by
  intro a ha had
  have h1 := h (c * a) (Nat.mul_pos hc ha) (by nlinarith)
  have e : d * c - c * a = c * (d - a) := by rw [mul_tsub, mul_comm d c]
  rw [e, ArithmeticFunction.liouville_apply_mul, ArithmeticFunction.liouville_apply_mul] at h1
  rcases liouville_sign hc with h2 | h2 <;> rw [h2] at h1 <;> linarith

/-! ### The even completion -/

def evenCompletion (p : ℕ) (f : ℕ → ℤ) (x : ZMod p) : ℤ := f x.valMinAbs.natAbs

theorem evenCompletion_nat {p n : ℕ} {f : ℕ → ℤ} (hhi : 2 * n < p) :
    evenCompletion p f (n : ZMod p) = f n := by
  have hc := ZMod.valMinAbs_natCast_of_le_half (show n ≤ p / 2 by omega)
  simp only [evenCompletion, hc, Int.natAbs_natCast]

theorem evenCompletion_neg {p : ℕ} {f : ℕ → ℤ} (hp2 : p % 2 = 1) (x : ZMod p) :
    evenCompletion p f (-x) = evenCompletion p f x := by
  have hne : 2 * x.val ≠ p := by omega
  simp [evenCompletion, ZMod.valMinAbs_neg_of_ne_half hne]

section Even

variable {p : ℕ} (hp2 : p % 2 = 1) (hAE : AllEqual p)
include hp2 hAE

theorem even_two_nat {n : ℕ} (hn : 0 < n) (hhi : 2 * n < p) :
    evenCompletion p liouville (2 * (n : ZMod p)) = -evenCompletion p liouville (n : ZMod p) := by
  rw [evenCompletion_nat hhi]
  by_cases h : 4 * n < p
  · have he : (2 : ZMod p) * n = ((2 * n : ℕ) : ZMod p) := by push_cast; rfl
    rw [he, evenCompletion_nat (by omega), liouville_mul_prime Nat.prime_two]
  · have he : (2 : ZMod p) * n = -((p - 2 * n : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (by omega : 2 * n ≤ p), ZMod.natCast_self]; push_cast; ring
    rw [he, evenCompletion_neg hp2, evenCompletion_nat (by omega),
      hAE (2 * n) (by omega) (by omega), liouville_mul_prime Nat.prime_two]

theorem even_two [NeZero p] (x : ZMod p) :
    evenCompletion p liouville (2 * x) = -evenCompletion p liouville x := by
  by_cases hx : x = 0
  · simp [hx, evenCompletion]
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h]; exact even_two_nat hp2 hAE hn hhi
  · rw [h, mul_neg, evenCompletion_neg hp2, evenCompletion_neg hp2, even_two_nat hp2 hAE hn hhi]

theorem even_three_nat (hp3 : p % 3 ≠ 0) {n : ℕ} (hn : 0 < n) (hhi : 2 * n < p) :
    evenCompletion p liouville (3 * (n : ZMod p)) = -evenCompletion p liouville (n : ZMod p) := by
  rw [evenCompletion_nat hhi]
  by_cases h6 : 6 * n < p
  · have he : (3 : ZMod p) * n = ((3 * n : ℕ) : ZMod p) := by push_cast; rfl
    rw [he, evenCompletion_nat (by omega), liouville_mul_prime Nat.prime_three]
  by_cases h3 : 3 * n < p
  · have he : (3 : ZMod p) * n = -((p - 3 * n : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (by omega : 3 * n ≤ p), ZMod.natCast_self]; push_cast; ring
    rw [he, evenCompletion_neg hp2, evenCompletion_nat (by omega), hAE (3 * n) (by omega) h3,
      liouville_mul_prime Nat.prime_three]
  · have he : (3 : ZMod p) * n = ((3 * n - p : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (by omega : p ≤ 3 * n), ZMod.natCast_self]; push_cast; ring
    rw [he, evenCompletion_nat (by omega)]
    have e1 := liouville_mul_prime Nat.prime_two (3 * n - p)
    have e2 := hAE (2 * (3 * n - p)) (by omega) (by omega)
    have e3 : p - 2 * (3 * n - p) = 3 * (p - 2 * n) := by omega
    rw [e3, liouville_mul_prime Nat.prime_three] at e2
    have e4 := hAE (2 * n) (by omega) (by omega)
    have e5 := liouville_mul_prime Nat.prime_two n
    linarith

theorem even_three [NeZero p] (hp3 : p % 3 ≠ 0) (x : ZMod p) :
    evenCompletion p liouville (3 * x) = -evenCompletion p liouville x := by
  by_cases hx : x = 0
  · simp [hx, evenCompletion]
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h]; exact even_three_nat hp2 hAE hp3 hn hhi
  · rw [h, mul_neg, evenCompletion_neg hp2, evenCompletion_neg hp2,
      even_three_nat hp2 hAE hp3 hn hhi]

omit hAE in
theorem even_sign [NeZero p] {x : ZMod p} (hx : x ≠ 0) :
    evenCompletion p liouville x = 1 ∨ evenCompletion p liouville x = -1 := by
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h, evenCompletion_nat hhi]; exact liouville_sign hn
  · rw [h, evenCompletion_neg hp2, evenCompletion_nat hhi]; exact liouville_sign hn

end Even

/-- The `p ≡ 1 (mod 4)` companion of the background `exists_prime_square_below_half`. -/
theorem exists_prime_square_below_half_one {p : ℕ} (hp : p.Prime) (hp13 : 13 ≤ p)
    (hp4 : p % 4 = 1) : ∃ ℓ : ℕ, ℓ.Prime ∧ 2 * ℓ < p ∧ IsSquare (ℓ : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases h8 : p % 8 = 1
  · exact ⟨2, Nat.prime_two, by omega,
      (ZMod.exists_sq_eq_two_iff (by omega : p ≠ 2)).mpr (Or.inl h8)⟩
  · let L := (p - 1) / 4
    have hL : 1 < L := by dsimp [L]; omega
    have hL4 : 4 * L = p - 1 := by dsimp [L]; omega
    obtain ⟨ℓ, hℓ, hℓL⟩ := Nat.exists_prime_and_dvd (by omega : L ≠ 1)
    let : Fact ℓ.Prime := ⟨hℓ⟩
    have hℓbound : ℓ ≤ L := Nat.le_of_dvd (by omega) hℓL
    refine ⟨ℓ, hℓ, by omega, ?_⟩
    have hℓ2 : ℓ ≠ 2 := by
      rintro rfl
      have : L % 2 = 0 := Nat.mod_eq_zero_of_dvd hℓL
      omega
    have hℓdiv : ℓ ∣ p - 1 := by rw [← hL4]; exact dvd_mul_of_dvd_right hℓL 4
    have hpcast : (p : ZMod ℓ) = 1 := by
      have hz := (ZMod.natCast_eq_zero_iff (p - 1) ℓ).mpr hℓdiv
      rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] at hz
      exact sub_eq_zero.mp hz
    apply (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := p) (q := ℓ) hp4 hℓ2).mpr
    rw [hpcast]
    exact ⟨1, by ring⟩

/-- No prime `p ≥ 7` has all pairs of equal sign. -/
theorem not_allEqual_prime {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hAE : AllEqual p) : False := by
  have hp2 : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hp3 : p % 3 ≠ 0 := by
    intro h
    have := (hp.dvd_iff_eq (by decide : (3 : ℕ) ≠ 1)).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  let : Fact p.Prime := ⟨hp⟩
  let G := evenCompletion p liouville
  have hG0 : G 0 = 0 := by simp [G, evenCompletion]
  have hG1 : G 1 = 1 := by
    have := evenCompletion_nat (p := p) (n := 1) (f := liouville) (by omega)
    simpa [G, ArithmeticFunction.liouville_apply_one] using this
  have hGneg : ∀ x, G (-x) = G x := evenCompletion_neg hp2
  have hGtwo : ∀ x, G (2 * x) = -G x := even_two hp2 hAE
  have hGthree : ∀ x, G (3 * x) = -G x := even_three hp2 hAE hp3
  have hm1 : G (-1) = 1 := by rw [hGneg, hG1]
  have h2 : G 2 = -1 := by simpa [hG1] using hGtwo 1
  have h3 : G 3 = -1 := by simpa [hG1] using hGthree 1
  have hsign : ∀ x : ZMod p, x ≠ 0 → G x = 1 ∨ G x = -1 := fun x hx => even_sign hp2 hx
  have hGnz : ∀ x : ZMod p, x ≠ 0 → G x ≠ 0 := by
    intro x hx
    rcases hsign x hx with h | h <;> omega
  have hminus : IsGood G (-1) := by
    intro x; rw [hm1, one_mul, neg_one_mul, hGneg]
  have htwo : IsGood G 2 := by
    intro x; rw [h2, hGtwo, neg_one_mul]
  have hthree : IsGood G 3 := by
    intro x; rw [h3, hGthree, neg_one_mul]
  have hlocal : ∀ a b : ℕ, 0 < a → 0 < b → 2 * (a * b) < p →
      G ((a * b : ℕ) : ZMod p) = G a * G b := by
    intro a b ha hb hab
    have ha' : a ≤ a * b := Nat.le_mul_of_pos_right a hb
    have hb' : b ≤ a * b := Nat.le_mul_of_pos_left b ha
    show evenCompletion p liouville _ = evenCompletion p liouville _ * evenCompletion p liouville _
    rw [evenCompletion_nat hab, evenCompletion_nat (by omega), evenCompletion_nat (by omega),
      ArithmeticFunction.liouville_apply_mul]
  have hmul := half_interval_extension_via_invariance p hp (by omega) G hG0 hG1 hGnz
    hminus htwo hthree hlocal
  obtain ⟨ℓ, hℓ, hℓp, hsq⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ 2 * ℓ < p ∧ IsSquare (ℓ : ZMod p) := by
    rcases (show p % 4 = 1 ∨ p % 4 = 3 by omega) with h4 | h4
    · exact exists_prime_square_below_half_one hp (by omega) h4
    · exact exists_prime_square_below_half hp (by omega) h4
  obtain ⟨s, hs⟩ := hsq
  have hl0 : ((ℓ : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd hℓ.pos hdvd
    omega
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact hl0 hs
  have hGl : G ℓ = 1 := by
    rw [hs, hmul]
    rcases hsign s hs0 with h | h <;> rw [h] <;> norm_num
  have hGl' : G ℓ = -1 := by
    show evenCompletion p liouville _ = _
    rw [evenCompletion_nat (by omega)]
    exact liouville_prime hℓ
  rw [hGl] at hGl'
  norm_num at hGl'

/-! ### Small cases and the descent -/

theorem not_allEqual_small {k : ℕ}
    (hk : k = 3 ∨ k = 4 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 20 ∨ k = 25) : ¬ AllEqual k := by
  have l1 : liouville 1 = 1 := ArithmeticFunction.liouville_apply_one
  have l2 : liouville 2 = -1 := liouville_prime Nat.prime_two
  have l3 : liouville 3 = -1 := liouville_prime Nat.prime_three
  have l5 : liouville 5 = -1 := liouville_prime (by norm_num)
  have l7 : liouville 7 = -1 := liouville_prime (by norm_num)
  have l19 : liouville 19 = -1 := liouville_prime (by norm_num)
  have l4 : liouville 4 = 1 := liouville_small (Or.inl rfl)
  have l8 : liouville 8 = -1 := by
    rw [show (8 : ℕ) = 2 * 4 by norm_num, liouville_mul_prime Nat.prime_two, l4]
  have l22 : liouville 22 = 1 := by
    rw [show (22 : ℕ) = 2 * 11 by norm_num, liouville_mul_prime Nat.prime_two,
      liouville_prime (by norm_num)]; norm_num
  intro h
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have := h 1 (by norm_num) (by norm_num); norm_num at this; rw [l2, l1] at this; norm_num at this
  · have := h 1 (by norm_num) (by norm_num); norm_num at this; rw [l3, l1] at this; norm_num at this
  · have := h 1 (by norm_num) (by norm_num); norm_num at this; rw [l5, l1] at this; norm_num at this
  · have := h 3 (by norm_num) (by norm_num); norm_num at this; rw [l4, l3] at this; norm_num at this
  · have := h 1 (by norm_num) (by norm_num); norm_num at this; rw [l7, l1] at this; norm_num at this
  · have := h 1 (by norm_num) (by norm_num); norm_num at this; rw [l8, l1] at this; norm_num at this
  · have := h 1 (by norm_num) (by norm_num); norm_num at this; rw [l19, l1] at this; norm_num at this
  · have := h 3 (by norm_num) (by norm_num); norm_num at this; rw [l22, l3] at this; norm_num at this

/-- Every `N ≥ 11` has a pair of unequal Liouville signs. -/
theorem not_allEqual : ∀ N, 11 ≤ N → ¬ AllEqual N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN hAE
  by_cases hev : N % 2 = 0
  · obtain ⟨m, rfl⟩ : ∃ m, N = m * 2 := ⟨N / 2, by omega⟩
    have hm := hAE.of_dvd (by norm_num : 0 < 2)
    by_cases h11 : 11 ≤ m
    · exact ih m (by omega) h11 hm
    · have : m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · exact not_allEqual_small (by norm_num) hm
      · exact not_allEqual_small (by norm_num) hm
      · exact not_allEqual_small (by norm_num) hm
      · exact not_allEqual_small (by norm_num) hm
      · exact not_allEqual_small (by norm_num) hAE
  · by_cases hpr : N.Prime
    · exact not_allEqual_prime hpr (by omega) hAE
    have hd := Nat.minFac_prime (show N ≠ 1 by omega)
    have hsq := Nat.minFac_sq_le_self (show 0 < N by omega) hpr
    obtain ⟨e, he⟩ := Nat.minFac_dvd N
    set d := N.minFac with hd_def
    have he0 : 0 < e := by rcases Nat.eq_zero_or_pos e with h | h <;> [simp [h] at he; exact h] <;> omega
    rw [he] at hAE
    have hAd := hAE.of_dvd he0
    have hd2 : d ≠ 2 := by
      intro h2; rw [h2] at he; omega
    by_cases hd7 : 7 ≤ d
    · exact not_allEqual_prime hd hd7 hAd
    have hd35 : d = 3 ∨ d = 5 := by
      have := hd.two_le
      have h4 : d ≠ 4 := by intro h; rw [h] at hd; exact absurd hd (by decide)
      have h6 : d ≠ 6 := by intro h; rw [h] at hd; exact absurd hd (by decide)
      omega
    rcases hd35 with h3 | h5
    · rw [h3] at hAd; exact not_allEqual_small (by norm_num) hAd
    · rw [h5] at he hsq hAE
      have hAe : AllEqual e := by
        rw [mul_comm] at hAE; exact hAE.of_dvd (by norm_num)
      have he5 : 5 ≤ e := by nlinarith
      by_cases he11 : 11 ≤ e
      · exact ih e (by omega) he11 hAe
      · have : e = 5 ∨ e = 7 ∨ e = 9 := by omega
        rcases this with rfl | rfl | rfl
        · exact not_allEqual_small (by norm_num) hAE
        · exact not_allEqual_small (by norm_num) hAe
        · exact not_allEqual_small (by norm_num) hAe

theorem mixedPair_of_ge {N : ℕ} (hN : 11 ≤ N) : SignPatterns.MixedPair N := by
  have h := not_allEqual N hN
  unfold AllEqual at h
  push_neg at h
  obtain ⟨a, ha, haN, hne⟩ := h
  rcases liouville_sign ha with h1 | h1 <;>
    rcases liouville_sign (show 0 < N - a by omega) with h2 | h2
  · exact absurd (h2.trans h1.symm) hne
  · exact ⟨a, N - a, ha, by omega, by omega, h1, h2⟩
  · exact ⟨N - a, a, by omega, ha, by omega, h2, h1⟩
  · exact absurd (h2.trans h1.symm) hne

/-- An equal-sign pair at every `N ≥ 11` (from the results already proved). -/
theorem equalPair_of_ge {N : ℕ} (hN : 11 ≤ N) :
    ∃ a, 0 < a ∧ a < N ∧ liouville a = liouville (N - a) := by
  by_cases hev : N % 2 = 0
  · obtain ⟨a, b, ha, hb, hab, h1, h2⟩ := liouville_goldbach N ⟨N / 2, by omega⟩ (by omega)
    refine ⟨a, ha, by omega, ?_⟩
    rw [show N - a = b by omega, h1, h2]
  · obtain ⟨a, b, ha, hb, hab, h1, h2⟩ :=
      equal_pair_odd (N := N) (by omega) (by omega) (by omega) (by omega) (e := 1) (Or.inl rfl)
    refine ⟨a, ha, by omega, ?_⟩
    rw [show N - a = b by omega, h1, h2]

/-- **Mangerel's nonextremality theorem** (IMRN 2024, Theorem 1.2), proved here from scratch. -/
theorem mangerel_nonextremality : SignPatterns.MangerelNonextremality := by
  intro m hm
  obtain ⟨a, b, ha, hb, hab, h1, h2⟩ := mixedPair_of_ge hm
  obtain ⟨c, hc, hcm, hceq⟩ := equalPair_of_ge hm
  have hmem : ∀ n, n ∈ Finset.Icc 1 (m - 1) ↔ 0 < n ∧ n < m := by
    intro n; simp only [Finset.mem_Icc]; omega
  have hpm : ∀ n ∈ Finset.Icc 1 (m - 1),
      liouville n * liouville (m - n) = 1 ∨ liouville n * liouville (m - n) = -1 := by
    intro n hn
    rw [hmem] at hn
    rcases liouville_sign hn.1 with h | h <;>
      rcases liouville_sign (show 0 < m - n by omega) with h' | h' <;> rw [h, h'] <;> norm_num
  have hcard : ((Finset.Icc 1 (m - 1)).card : ℤ) = (m : ℤ) - 1 := by
    rw [Nat.card_Icc, show m - 1 + 1 - 1 = m - 1 by omega, Nat.cast_sub (by omega)]
    norm_num
  have hA : liouville a * liouville (m - a) = -1 := by
    rw [show m - a = b by omega, h1, h2]; norm_num
  have hC : liouville c * liouville (m - c) = 1 := by
    rw [← hceq]; rcases liouville_sign hc with h | h <;> rw [h] <;> norm_num
  have hup := Finset.single_le_sum (f := fun n => 1 - liouville n * liouville (m - n))
    (fun n hn => by rcases hpm n hn with h | h <;> simp only [h] <;> norm_num)
    ((hmem a).mpr ⟨ha, by omega⟩)
  have hlo := Finset.single_le_sum (f := fun n => 1 + liouville n * liouville (m - n))
    (fun n hn => by rcases hpm n hn with h | h <;> simp only [h] <;> norm_num)
    ((hmem c).mpr ⟨hc, hcm⟩)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hcard, hA] at hup
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hcard, hC] at hlo
  rw [abs_lt]
  constructor <;> linarith

/-- **Theorem C, unconditional.** Every `N ≥ 2` outside `{2,3,4,5,6,9,10}` exhibits all four
Liouville sign patterns. -/
theorem all_four_patterns_unconditional {N : ℕ} (hN : 2 ≤ N)
    (h2 : N ≠ 2) (h3 : N ≠ 3) (h4 : N ≠ 4) (h5 : N ≠ 5) (h6 : N ≠ 6) (h9 : N ≠ 9)
    (h10 : N ≠ 10) {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    SignPair N s t :=
  all_four_patterns mangerel_nonextremality hN h2 h3 h4 h5 h6 h9 h10 hs ht

end OddCase
