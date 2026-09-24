import OddCase.Phi
import LiouvilleGoldbach

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-!
# Theorem B: both equal-sign Liouville pairs at every prime `p ≥ 5`

The one-exclusion rigidity (`OneExcl.exact_bands`) is fed with `g = e · λ`; the two exact band
identities then give exact multiplication by 2 and 3 for the odd completion, and the final
contradiction reuses the background development verbatim (`half_interval_extension_via_invariance`,
`no_multiplicative_agreement_of_odd`).
-/

namespace OddCase

open LiouvilleGoldbach LiouvilleGoldbach.Final

theorem liouville_mul_prime {q : ℕ} (hq : q.Prime) (n : ℕ) :
    liouville (q * n) = - liouville n := by
  rw [ArithmeticFunction.liouville_apply_mul, liouville_prime hq, neg_one_mul]

theorem oneExcl_of_noPair {p : ℕ} {e : ℤ} (he : e = 1 ∨ e = -1)
    (hno : ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = p ∧ liouville a = e ∧ liouville b = e) :
    OneExcl p (fun n => e * liouville n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn _
    show e * liouville n = 1 ∨ e * liouville n = -1
    rcases liouville_sign hn with h | h <;> rcases he with rfl | rfl <;> simp [h]
  · intro n _ _
    show e * liouville (2 * n) = -(e * liouville n)
    rw [liouville_mul_prime Nat.prime_two]; ring
  · intro n _ _
    show e * liouville (3 * n) = -(e * liouville n)
    rw [liouville_mul_prime Nat.prime_three]; ring
  · intro n _ _
    show e * liouville (5 * n) = -(e * liouville n)
    rw [liouville_mul_prime (by norm_num : Nat.Prime 5)]; ring
  · intro a b ha hb hab h
    have h1 : e * liouville a = 1 := h.1
    have h2 : e * liouville b = 1 := h.2
    apply hno
    refine ⟨a, b, ha, hb, hab, ?_, ?_⟩
    · rcases liouville_sign ha with h' | h' <;> rcases he with rfl | rfl <;> omega
    · rcases liouville_sign hb with h' | h' <;> rcases he with rfl | rfl <;> omega

theorem liouville_bands {p : ℕ} (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0) (hp7 : p % 7 ≠ 0)
    {e : ℤ} (he : e = 1 ∨ e = -1)
    (hno : ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = p ∧ liouville a = e ∧ liouville b = e) :
    (∀ n, p < 4 * n → 2 * n < p → liouville (p - 2 * n) = liouville n) ∧
    (∀ n, p < 3 * n → 2 * n < p → liouville (3 * n - p) = - liouville n) := by
  have H := oneExcl_of_noPair he hno
  obtain ⟨h1, h2⟩ := H.exact_bands hp2 hp3 hp7
  refine ⟨fun n a b => ?_, fun n a b => ?_⟩
  · have h : e * liouville (p - 2 * n) = e * liouville n := h1 n a b
    rcases he with rfl | rfl <;> linarith
  · have h : e * liouville (3 * n - p) = -(e * liouville n) := h2 n a b
    rcases he with rfl | rfl <;> linarith

/-! ### Bridge: exact band identities give exact ×2, ×3 for the odd completion
(adapted from the background `Completion.lean`, with the two-exclusion bands replaced). -/

section Bridge

variable {p : ℕ}

theorem completion_two_nat (hp2 : p % 2 = 1)
    (hc : ∀ n, p < 4 * n → 2 * n < p → liouville (p - 2 * n) = liouville n)
    {n : ℕ} (hn : 0 < n) (hhi : 2 * n < p) :
    oddCompletion p liouville (2 * (n : ZMod p)) = -oddCompletion p liouville (n : ZMod p) := by
  rw [oddCompletion_nat hn hhi]
  by_cases h : 4 * n < p
  · have he : (2 : ZMod p) * n = ((2 * n : ℕ) : ZMod p) := by push_cast; rfl
    rw [he, oddCompletion_nat (by omega) (by omega), liouville_mul_prime Nat.prime_two]
  · have hp4 : p < 4 * n := by omega
    have he : (2 : ZMod p) * n = -((p - 2 * n : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (by omega : 2 * n ≤ p), ZMod.natCast_self]
      push_cast
      ring
    rw [he, oddCompletion_neg hp2, oddCompletion_nat (by omega) (by omega), hc n hp4 hhi]

theorem completion_two [NeZero p] (hp2 : p % 2 = 1)
    (hc : ∀ n, p < 4 * n → 2 * n < p → liouville (p - 2 * n) = liouville n) (x : ZMod p) :
    oddCompletion p liouville (2 * x) = -oddCompletion p liouville x := by
  by_cases hx : x = 0
  · simp [hx, oddCompletion_zero]
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h]; exact completion_two_nat hp2 hc hn hhi
  · rw [h, mul_neg, oddCompletion_neg hp2, oddCompletion_neg hp2,
      completion_two_nat hp2 hc hn hhi]

theorem completion_neg_two [NeZero p] (hp2 : p % 2 = 1)
    (hc : ∀ n, p < 4 * n → 2 * n < p → liouville (p - 2 * n) = liouville n) (x : ZMod p) :
    oddCompletion p liouville (-2 * x) = oddCompletion p liouville x := by
  rw [neg_mul, oddCompletion_neg hp2, completion_two hp2 hc, neg_neg]

theorem completion_three_upper
    (hu : ∀ n, p < 3 * n → 2 * n < p → liouville (3 * n - p) = - liouville n)
    {n : ℕ} (hlo : p < 3 * n) (hhi : 2 * n < p) :
    oddCompletion p liouville (3 * (n : ZMod p)) = -oddCompletion p liouville (n : ZMod p) := by
  have he : (3 : ZMod p) * n = ((3 * n - p : ℕ) : ZMod p) := by
    rw [Nat.cast_sub (by omega : p ≤ 3 * n), ZMod.natCast_self]
    push_cast
    ring
  rw [he, oddCompletion_nat (by omega) (by omega), oddCompletion_nat (by omega) hhi,
    hu n hlo hhi]

theorem completion_three_nat [NeZero p] (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0)
    (hc : ∀ n, p < 4 * n → 2 * n < p → liouville (p - 2 * n) = liouville n)
    (hu : ∀ n, p < 3 * n → 2 * n < p → liouville (3 * n - p) = - liouville n)
    {n : ℕ} (hn : 0 < n) (hhi : 2 * n < p) :
    oddCompletion p liouville (3 * (n : ZMod p)) = -oddCompletion p liouville (n : ZMod p) := by
  by_cases hlo : 6 * n < p
  · have he : (3 : ZMod p) * n = ((3 * n : ℕ) : ZMod p) := by push_cast; rfl
    rw [he, oddCompletion_nat (by omega) (by omega), oddCompletion_nat hn hhi,
      liouville_mul_prime Nat.prime_three]
  by_cases hup : p < 3 * n
  · exact completion_three_upper hu hup hhi
  have hnlo : p < 6 * n := by omega
  have hnhi : 3 * n < p := by omega
  by_cases hsmall : 4 * n < p
  · have hupper := completion_three_upper hu
      (show p < 3 * (2 * n) by omega) (show 2 * (2 * n) < p by omega)
    have he : ((2 * n : ℕ) : ZMod p) = 2 * (n : ZMod p) := by push_cast; rfl
    rw [he] at hupper
    have he2 : 3 * (2 * (n : ZMod p)) = 2 * (3 * (n : ZMod p)) := by ring
    rw [he2, completion_two hp2 hc, completion_two hp2 hc] at hupper
    omega
  · have hupper := completion_three_upper hu
      (show p < 3 * (p - 2 * n) by omega) (show 2 * (p - 2 * n) < p by omega)
    have he : ((p - 2 * n : ℕ) : ZMod p) = -2 * (n : ZMod p) := by
      rw [Nat.cast_sub (by omega : 2 * n ≤ p), ZMod.natCast_self]
      push_cast
      ring
    rw [he] at hupper
    have he2 : 3 * (-2 * (n : ZMod p)) = -2 * (3 * (n : ZMod p)) := by ring
    rw [he2, completion_neg_two hp2 hc, completion_neg_two hp2 hc] at hupper
    exact hupper

theorem completion_three [NeZero p] (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0)
    (hc : ∀ n, p < 4 * n → 2 * n < p → liouville (p - 2 * n) = liouville n)
    (hu : ∀ n, p < 3 * n → 2 * n < p → liouville (3 * n - p) = - liouville n) (x : ZMod p) :
    oddCompletion p liouville (3 * x) = -oddCompletion p liouville x := by
  by_cases hx : x = 0
  · simp [hx, oddCompletion_zero]
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h]; exact completion_three_nat hp2 hp3 hc hu hn hhi
  · rw [h, mul_neg, oddCompletion_neg hp2, oddCompletion_neg hp2,
      completion_three_nat hp2 hp3 hc hu hn hhi]

theorem completion_sign [NeZero p] (hp2 : p % 2 = 1) {x : ZMod p} (hx : x ≠ 0) :
    oddCompletion p liouville x = 1 ∨ oddCompletion p liouville x = -1 := by
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h, oddCompletion_nat hn hhi]; exact liouville_sign hn
  · rw [h, oddCompletion_neg hp2, oddCompletion_nat hn hhi]
    rcases liouville_sign hn with h1 | h1 <;> omega

end Bridge

/-! ### Theorem B -/

theorem liouville_small {n : ℕ} : n = 4 ∨ n = 6 → liouville n = 1 := by
  rintro (rfl | rfl)
  · rw [show (4 : ℕ) = 2 * 2 from rfl, liouville_mul_prime Nat.prime_two,
      liouville_prime Nat.prime_two]; norm_num
  · rw [show (6 : ℕ) = 2 * 3 from rfl, liouville_mul_prime Nat.prime_two,
      liouville_prime Nat.prime_three]; norm_num

/-- **Theorem B.** Every prime `p ≥ 5` is a sum of two positive integers of equal Liouville
sign `e`, for each `e = ±1`. -/
theorem equal_pair_at_prime {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {e : ℤ} (he : e = 1 ∨ e = -1) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = p ∧ liouville a = e ∧ liouville b = e := by
  have hp2 : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hp3 : p % 3 ≠ 0 := by
    intro h
    have := (hp.dvd_iff_eq (by decide : (3 : ℕ) ≠ 1)).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have l1 : liouville 1 = 1 := ArithmeticFunction.liouville_apply_one
  by_cases h57 : p = 5 ∨ p = 7
  · rcases h57 with rfl | rfl <;> rcases he with rfl | rfl
    · exact ⟨1, 4, by omega, by omega, rfl, l1, liouville_small (Or.inl rfl)⟩
    · exact ⟨2, 3, by omega, by omega, rfl, liouville_prime Nat.prime_two,
        liouville_prime Nat.prime_three⟩
    · exact ⟨1, 6, by omega, by omega, rfl, l1, liouville_small (Or.inr rfl)⟩
    · exact ⟨2, 5, by omega, by omega, rfl, liouville_prime Nat.prime_two,
        liouville_prime (by norm_num)⟩
  have hp7 : p % 7 ≠ 0 := by
    intro h
    have := (hp.dvd_iff_eq (by decide : (7 : ℕ) ≠ 1)).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  by_contra hno
  obtain ⟨hc, hu⟩ := liouville_bands hp2 hp3 hp7 he hno
  let : Fact p.Prime := ⟨hp⟩
  let F := oddCompletion p liouville
  have hF0 : F 0 = 0 := oddCompletion_zero p liouville
  have hF1 : F 1 = 1 := oddCompletion_one (by omega) ArithmeticFunction.liouville_apply_one
  have hFneg : ∀ x, F (-x) = -F x := oddCompletion_neg hp2
  have hFtwo : ∀ x, F (2 * x) = -F x := completion_two hp2 hc
  have hFthree : ∀ x, F (3 * x) = -F x := completion_three hp2 hp3 hc hu
  have hm1 : F (-1) = -1 := by simpa [hF1] using hFneg 1
  have h2 : F 2 = -1 := by simpa [hF1] using hFtwo 1
  have h3 : F 3 = -1 := by simpa [hF1] using hFthree 1
  have hsign : ∀ x : ZMod p, x ≠ 0 → F x = 1 ∨ F x = -1 := fun x hx => completion_sign hp2 hx
  have hFnz : ∀ x : ZMod p, x ≠ 0 → F x ≠ 0 := by
    intro x hx
    rcases hsign x hx with hs | hs <;> omega
  have hminus : IsGood F (-1) := by
    intro x
    simpa [hm1] using hFneg x
  have htwo : IsGood F 2 := by
    intro x
    simpa [h2] using hFtwo x
  have hthree : IsGood F 3 := by
    intro x
    simpa [h3] using hFthree x
  have hlocal : ∀ a b : ℕ, 0 < a → 0 < b → 2 * (a * b) < p →
      F ((a * b : ℕ) : ZMod p) = F a * F b := by
    intro a b ha hb hab
    simpa only [Nat.cast_mul] using
      oddCompletion_short_mul ArithmeticFunction.liouville_apply_mul ha hb hab
  have hmul := half_interval_extension_via_invariance p hp (by omega) F hF0 hF1 hFnz
    hminus htwo hthree hlocal
  exact no_multiplicative_agreement_of_odd hp (by omega) F (fun x y _ _ => hmul x y)
    hsign hm1 (fun n hn hnp => oddCompletion_nat hn hnp)

end OddCase
