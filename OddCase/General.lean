import OddCase.Mixed

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-!
# Theorem F: the Legendre symbol is the only obstruction

The one-exclusion rigidity uses the Liouville function only through complete multiplicativity and
the values at 2, 3, 5. For any completely multiplicative `f : ℕ → ℤ` with values `±1` on positive
integers and `f 2 = f 3 = f 5 = -1`, a prime `p ≥ 11` with no `a + b = p`, `f a = f b = e`, forces
`p ≡ 3 (mod 4)` and `f n = (n / p)` (Legendre symbol) for every `0 < n < p/2`; a prime `p ≥ 7`
with no `a + b = p`, `f a ≠ f b` (only `f 2 = f 3 = -1` needed) forces `p ≡ 1 (mod 4)` and the same
agreement. The final contradiction of the Liouville case is replaced by a classification step
(`eq_legendre_of_mul`, `eq_legendre_of_mul'`).
-/

namespace OddCase

open LiouvilleGoldbach

section General

variable {f : ℕ → ℤ}

theorem oneExcl_of_noPair_gen (hsign : ∀ n, 0 < n → f n = 1 ∨ f n = -1)
    (hmul : ∀ a b, f (a * b) = f a * f b) (h2 : f 2 = -1) (h3 : f 3 = -1) (h5 : f 5 = -1)
    {p : ℕ} {e : ℤ} (he : e = 1 ∨ e = -1)
    (hno : ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = p ∧ f a = e ∧ f b = e) :
    OneExcl p (fun n => e * f n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn _
    show e * f n = 1 ∨ e * f n = -1
    rcases hsign n hn with h | h <;> rcases he with rfl | rfl <;> simp [h]
  · intro n _ _
    show e * f (2 * n) = -(e * f n)
    rw [hmul, h2]; ring
  · intro n _ _
    show e * f (3 * n) = -(e * f n)
    rw [hmul, h3]; ring
  · intro n _ _
    show e * f (5 * n) = -(e * f n)
    rw [hmul, h5]; ring
  · intro a b ha hb hab h
    have h1 : e * f a = 1 := h.1
    have h2' : e * f b = 1 := h.2
    apply hno
    refine ⟨a, b, ha, hb, hab, ?_, ?_⟩
    · rcases hsign a ha with h' | h' <;> rcases he with rfl | rfl <;> simp_all
    · rcases hsign b hb with h' | h' <;> rcases he with rfl | rfl <;> simp_all

theorem bands_gen (hsign : ∀ n, 0 < n → f n = 1 ∨ f n = -1)
    (hmul : ∀ a b, f (a * b) = f a * f b) (h2 : f 2 = -1) (h3 : f 3 = -1) (h5 : f 5 = -1)
    {p : ℕ} (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0) (hp7 : p % 7 ≠ 0)
    {e : ℤ} (he : e = 1 ∨ e = -1)
    (hno : ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = p ∧ f a = e ∧ f b = e) :
    (∀ n, p < 4 * n → 2 * n < p → f (p - 2 * n) = f n) ∧
    (∀ n, p < 3 * n → 2 * n < p → f (3 * n - p) = - f n) := by
  have H := oneExcl_of_noPair_gen hsign hmul h2 h3 h5 he hno
  obtain ⟨h1, h2'⟩ := H.exact_bands hp2 hp3 hp7
  refine ⟨fun n a b => ?_, fun n a b => ?_⟩
  · have h : e * f (p - 2 * n) = e * f n := h1 n a b
    rcases he with rfl | rfl <;> linarith
  · have h : e * f (3 * n - p) = -(e * f n) := h2' n a b
    rcases he with rfl | rfl <;> linarith

variable {p : ℕ}

theorem gcompletion_two_nat (hmul : ∀ a b, f (a * b) = f a * f b) (h2 : f 2 = -1)
    (hp2 : p % 2 = 1)
    (hc : ∀ n, p < 4 * n → 2 * n < p → f (p - 2 * n) = f n)
    {n : ℕ} (hn : 0 < n) (hhi : 2 * n < p) :
    oddCompletion p f (2 * (n : ZMod p)) = -oddCompletion p f (n : ZMod p) := by
  rw [oddCompletion_nat hn hhi]
  by_cases h : 4 * n < p
  · have he : (2 : ZMod p) * n = ((2 * n : ℕ) : ZMod p) := by push_cast; rfl
    rw [he, oddCompletion_nat (by omega) (by omega), hmul, h2]; ring
  · have hp4 : p < 4 * n := by omega
    have he : (2 : ZMod p) * n = -((p - 2 * n : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (by omega : 2 * n ≤ p), ZMod.natCast_self]
      push_cast
      ring
    rw [he, oddCompletion_neg hp2, oddCompletion_nat (by omega) (by omega), hc n hp4 hhi]

theorem gcompletion_two [NeZero p] (hmul : ∀ a b, f (a * b) = f a * f b) (h2 : f 2 = -1)
    (hp2 : p % 2 = 1)
    (hc : ∀ n, p < 4 * n → 2 * n < p → f (p - 2 * n) = f n) (x : ZMod p) :
    oddCompletion p f (2 * x) = -oddCompletion p f x := by
  by_cases hx : x = 0
  · simp [hx, oddCompletion_zero]
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h]; exact gcompletion_two_nat hmul h2 hp2 hc hn hhi
  · rw [h, mul_neg, oddCompletion_neg hp2, oddCompletion_neg hp2,
      gcompletion_two_nat hmul h2 hp2 hc hn hhi]

theorem gcompletion_neg_two [NeZero p] (hmul : ∀ a b, f (a * b) = f a * f b) (h2 : f 2 = -1)
    (hp2 : p % 2 = 1)
    (hc : ∀ n, p < 4 * n → 2 * n < p → f (p - 2 * n) = f n) (x : ZMod p) :
    oddCompletion p f (-2 * x) = oddCompletion p f x := by
  rw [neg_mul, oddCompletion_neg hp2, gcompletion_two hmul h2 hp2 hc, neg_neg]

theorem gcompletion_three_upper
    (hu : ∀ n, p < 3 * n → 2 * n < p → f (3 * n - p) = - f n)
    {n : ℕ} (hlo : p < 3 * n) (hhi : 2 * n < p) :
    oddCompletion p f (3 * (n : ZMod p)) = -oddCompletion p f (n : ZMod p) := by
  have he : (3 : ZMod p) * n = ((3 * n - p : ℕ) : ZMod p) := by
    rw [Nat.cast_sub (by omega : p ≤ 3 * n), ZMod.natCast_self]
    push_cast
    ring
  rw [he, oddCompletion_nat (by omega) (by omega), oddCompletion_nat (by omega) hhi,
    hu n hlo hhi]

theorem gcompletion_three_nat [NeZero p] (hmul : ∀ a b, f (a * b) = f a * f b)
    (h2 : f 2 = -1) (h3 : f 3 = -1) (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0)
    (hc : ∀ n, p < 4 * n → 2 * n < p → f (p - 2 * n) = f n)
    (hu : ∀ n, p < 3 * n → 2 * n < p → f (3 * n - p) = - f n)
    {n : ℕ} (hn : 0 < n) (hhi : 2 * n < p) :
    oddCompletion p f (3 * (n : ZMod p)) = -oddCompletion p f (n : ZMod p) := by
  by_cases hlo : 6 * n < p
  · have he : (3 : ZMod p) * n = ((3 * n : ℕ) : ZMod p) := by push_cast; rfl
    rw [he, oddCompletion_nat (by omega) (by omega), oddCompletion_nat hn hhi, hmul, h3]; ring
  by_cases hup : p < 3 * n
  · exact gcompletion_three_upper hu hup hhi
  have hnlo : p < 6 * n := by omega
  have hnhi : 3 * n < p := by omega
  by_cases hsmall : 4 * n < p
  · have hupper := gcompletion_three_upper hu
      (show p < 3 * (2 * n) by omega) (show 2 * (2 * n) < p by omega)
    have he : ((2 * n : ℕ) : ZMod p) = 2 * (n : ZMod p) := by push_cast; rfl
    rw [he] at hupper
    have he2 : 3 * (2 * (n : ZMod p)) = 2 * (3 * (n : ZMod p)) := by ring
    rw [he2, gcompletion_two hmul h2 hp2 hc, gcompletion_two hmul h2 hp2 hc] at hupper
    omega
  · have hupper := gcompletion_three_upper hu
      (show p < 3 * (p - 2 * n) by omega) (show 2 * (p - 2 * n) < p by omega)
    have he : ((p - 2 * n : ℕ) : ZMod p) = -2 * (n : ZMod p) := by
      rw [Nat.cast_sub (by omega : 2 * n ≤ p), ZMod.natCast_self]
      push_cast
      ring
    rw [he] at hupper
    have he2 : 3 * (-2 * (n : ZMod p)) = -2 * (3 * (n : ZMod p)) := by ring
    rw [he2, gcompletion_neg_two hmul h2 hp2 hc, gcompletion_neg_two hmul h2 hp2 hc] at hupper
    exact hupper

theorem gcompletion_three [NeZero p] (hmul : ∀ a b, f (a * b) = f a * f b)
    (h2 : f 2 = -1) (h3 : f 3 = -1) (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0)
    (hc : ∀ n, p < 4 * n → 2 * n < p → f (p - 2 * n) = f n)
    (hu : ∀ n, p < 3 * n → 2 * n < p → f (3 * n - p) = - f n) (x : ZMod p) :
    oddCompletion p f (3 * x) = -oddCompletion p f x := by
  by_cases hx : x = 0
  · simp [hx, oddCompletion_zero]
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h]; exact gcompletion_three_nat hmul h2 h3 hp2 hp3 hc hu hn hhi
  · rw [h, mul_neg, oddCompletion_neg hp2, oddCompletion_neg hp2,
      gcompletion_three_nat hmul h2 h3 hp2 hp3 hc hu hn hhi]

theorem gcompletion_sign [NeZero p] (hsign : ∀ n, 0 < n → f n = 1 ∨ f n = -1)
    (hp2 : p % 2 = 1) {x : ZMod p} (hx : x ≠ 0) :
    oddCompletion p f x = 1 ∨ oddCompletion p f x = -1 := by
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h, oddCompletion_nat hn hhi]; exact hsign n hn
  · rw [h, oddCompletion_neg hp2, oddCompletion_nat hn hhi]
    rcases hsign n hn with h1 | h1 <;> omega

end General

/-! ### Multiplicative ±1 functions on `ZMod p` with `F (-1) = -1` are the Legendre symbol -/

theorem eq_legendre_of_mul {p : ℕ} [Fact p.Prime] (F : ZMod p → ℤ)
    (hmul : ∀ x y : ZMod p, F (x * y) = F x * F y)
    (hsign : ∀ x : ZMod p, x ≠ 0 → F x = 1 ∨ F x = -1)
    (hneg : F (-1) = -1) :
    p % 4 = 3 ∧ ∀ x : ZMod p, x ≠ 0 → F x = legendreSym p x.val := by
  have hsq : ∀ y : ZMod p, y ≠ 0 → F (y * y) = 1 := by
    intro y hy
    rw [hmul]; rcases hsign y hy with h | h <;> rw [h] <;> norm_num
  -- -1 is not a square
  have hns : ¬ IsSquare (-1 : ZMod p) := by
    rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have := hsq y hy0
    rw [← hy, hneg] at this; norm_num at this
  have h4 : p % 4 = 3 := by
    by_contra h
    exact hns (ZMod.exists_sq_eq_neg_one_iff.mpr h)
  refine ⟨h4, fun x hx => ?_⟩
  have hxv : ((x.val : ℤ) : ZMod p) = x := by simp
  by_cases hxs : IsSquare x
  · obtain ⟨y, hy⟩ := hxs
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; exact hx hy
    have hFx : F x = 1 := by rw [hy]; exact hsq y hy0
    rw [hFx]
    symm
    rw [legendreSym.eq_one_iff p (by rw [hxv]; exact hx)]
    rw [hxv]; exact ⟨y, hy⟩
  · -- -x is a square, since the Legendre symbol is multiplicative
    have hl : legendreSym p x.val = -1 := by
      rw [legendreSym.eq_neg_one_iff p]; rw [hxv]; exact hxs
    have hlm : legendreSym p (-1) = -1 := by
      rw [legendreSym.eq_neg_one_iff p]; simpa using hns
    have hmx : IsSquare (-x) := by
      have h1 : legendreSym p ((-1) * (x.val : ℤ)) = 1 := by
        rw [legendreSym.mul, hlm, hl]; norm_num
      have hne : (((-1) * (x.val : ℤ) : ℤ) : ZMod p) ≠ 0 := by
        push_cast; rw [ZMod.natCast_zmod_val]; simpa using hx
      have := (legendreSym.eq_one_iff p hne).mp h1
      push_cast at this; rwa [ZMod.natCast_zmod_val, neg_one_mul] at this
    obtain ⟨y, hy⟩ := hmx
    have hy0 : y ≠ 0 := by
      rintro rfl; simp at hy; exact hx hy
    have hfx : F (-x) = 1 := by rw [hy, hsq y hy0]
    have : F (-x) = F (-1) * F x := by rw [← hmul, neg_one_mul]
    rw [hfx, hneg] at this
    rw [hl]
    rcases hsign x hx with h | h
    · rw [h] at this; norm_num at this
    · exact h

/-- **Theorem F.** Let `f` be completely multiplicative, `±1` on positive integers, with
`f 2 = f 3 = f 5 = -1`. If a prime `p ≥ 11` has no `a + b = p` with `f a = f b = e`, then
`p ≡ 3 (mod 4)` and `f` agrees with the Legendre symbol mod `p` on `(0, p/2)`. -/
theorem legendre_of_no_equal_pair {f : ℕ → ℤ} (hf1 : f 1 = 1)
    (hsign : ∀ n, 0 < n → f n = 1 ∨ f n = -1)
    (hmul : ∀ a b, f (a * b) = f a * f b) (h2 : f 2 = -1) (h3 : f 3 = -1) (h5 : f 5 = -1)
    {p : ℕ} [Fact p.Prime] (hp11 : 11 ≤ p) {e : ℤ} (he : e = 1 ∨ e = -1)
    (hno : ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = p ∧ f a = e ∧ f b = e) :
    p % 4 = 3 ∧ ∀ n : ℕ, 0 < n → 2 * n < p → f n = legendreSym p n := by
  have hp : p.Prime := Fact.out
  have hp2 : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hp3 : p % 3 ≠ 0 := by
    intro h
    have := (hp.dvd_iff_eq (by decide : (3 : ℕ) ≠ 1)).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have hp7 : p % 7 ≠ 0 := by
    intro h
    have := (hp.dvd_iff_eq (by decide : (7 : ℕ) ≠ 1)).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  obtain ⟨hc, hu⟩ := bands_gen hsign hmul h2 h3 h5 hp2 hp3 hp7 he hno
  let F := oddCompletion p f
  have hF0 : F 0 = 0 := oddCompletion_zero p f
  have hF1 : F 1 = 1 := oddCompletion_one (by omega) hf1
  have hFneg : ∀ x, F (-x) = -F x := oddCompletion_neg hp2
  have hFtwo : ∀ x, F (2 * x) = -F x := gcompletion_two hmul h2 hp2 hc
  have hFthree : ∀ x, F (3 * x) = -F x := gcompletion_three hmul h2 h3 hp2 hp3 hc hu
  have hm1 : F (-1) = -1 := by simpa [hF1] using hFneg 1
  have hF2 : F 2 = -1 := by simpa [hF1] using hFtwo 1
  have hF3 : F 3 = -1 := by simpa [hF1] using hFthree 1
  have hsgn : ∀ x : ZMod p, x ≠ 0 → F x = 1 ∨ F x = -1 :=
    fun x hx => gcompletion_sign hsign hp2 hx
  have hFnz : ∀ x : ZMod p, x ≠ 0 → F x ≠ 0 := by
    intro x hx
    rcases hsgn x hx with hs | hs <;> omega
  have hminus : IsGood F (-1) := by
    intro x
    simpa [hm1] using hFneg x
  have htwo : IsGood F 2 := by
    intro x
    simpa [hF2] using hFtwo x
  have hthree : IsGood F 3 := by
    intro x
    simpa [hF3] using hFthree x
  have hlocal : ∀ a b : ℕ, 0 < a → 0 < b → 2 * (a * b) < p →
      F ((a * b : ℕ) : ZMod p) = F a * F b := by
    intro a b ha hb hab
    simpa only [Nat.cast_mul] using oddCompletion_short_mul hmul ha hb hab
  have hmulF := half_interval_extension_via_invariance p hp (by omega) F hF0 hF1 hFnz
    hminus htwo hthree hlocal
  obtain ⟨h4, hleg⟩ := eq_legendre_of_mul F hmulF hsgn hm1
  refine ⟨h4, fun n hn hhi => ?_⟩
  have hnz : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd; exact absurd (Nat.le_of_dvd hn hd) (by omega)
  have := hleg n hnz
  have e1 : F (n : ZMod p) = f n := oddCompletion_nat hn hhi
  rw [e1, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
  exact this

/-! ### The mixed patterns: the even completion -/

section GeneralEven

variable {f : ℕ → ℤ} {p : ℕ}

/-- Every pair at `p` has equal `f`-signs. -/
def AllEqualF (f : ℕ → ℤ) (p : ℕ) : Prop := ∀ a, 0 < a → a < p → f (p - a) = f a

theorem geven_two_nat (hmul : ∀ a b, f (a * b) = f a * f b) (h2 : f 2 = -1)
    (hp2 : p % 2 = 1) (hAE : AllEqualF f p) {n : ℕ} (hn : 0 < n) (hhi : 2 * n < p) :
    evenCompletion p f (2 * (n : ZMod p)) = -evenCompletion p f (n : ZMod p) := by
  rw [evenCompletion_nat hhi]
  by_cases h : 4 * n < p
  · have he : (2 : ZMod p) * n = ((2 * n : ℕ) : ZMod p) := by push_cast; rfl
    rw [he, evenCompletion_nat (by omega), hmul, h2]; ring
  · have he : (2 : ZMod p) * n = -((p - 2 * n : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (by omega : 2 * n ≤ p), ZMod.natCast_self]; push_cast; ring
    rw [he, evenCompletion_neg hp2, evenCompletion_nat (by omega),
      hAE (2 * n) (by omega) (by omega), hmul, h2]; ring

theorem geven_two [NeZero p] (hmul : ∀ a b, f (a * b) = f a * f b) (h2 : f 2 = -1)
    (hp2 : p % 2 = 1) (hAE : AllEqualF f p) (x : ZMod p) :
    evenCompletion p f (2 * x) = -evenCompletion p f x := by
  by_cases hx : x = 0
  · have h := hmul 0 2; rw [zero_mul, h2] at h
    simp [hx, evenCompletion]; linarith
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h]; exact geven_two_nat hmul h2 hp2 hAE hn hhi
  · rw [h, mul_neg, evenCompletion_neg hp2, evenCompletion_neg hp2,
      geven_two_nat hmul h2 hp2 hAE hn hhi]

theorem geven_three_nat (hmul : ∀ a b, f (a * b) = f a * f b) (h2 : f 2 = -1) (h3 : f 3 = -1)
    (hp2 : p % 2 = 1) (hAE : AllEqualF f p) (hp3 : p % 3 ≠ 0) {n : ℕ} (hn : 0 < n)
    (hhi : 2 * n < p) :
    evenCompletion p f (3 * (n : ZMod p)) = -evenCompletion p f (n : ZMod p) := by
  rw [evenCompletion_nat hhi]
  by_cases h6 : 6 * n < p
  · have he : (3 : ZMod p) * n = ((3 * n : ℕ) : ZMod p) := by push_cast; rfl
    rw [he, evenCompletion_nat (by omega), hmul, h3]; ring
  by_cases h3' : 3 * n < p
  · have he : (3 : ZMod p) * n = -((p - 3 * n : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (by omega : 3 * n ≤ p), ZMod.natCast_self]; push_cast; ring
    rw [he, evenCompletion_neg hp2, evenCompletion_nat (by omega), hAE (3 * n) (by omega) h3',
      hmul, h3]; ring
  · have he : (3 : ZMod p) * n = ((3 * n - p : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (by omega : p ≤ 3 * n), ZMod.natCast_self]; push_cast; ring
    rw [he, evenCompletion_nat (by omega)]
    have e1 : f (2 * (3 * n - p)) = f 2 * f (3 * n - p) := hmul _ _
    have e2 := hAE (2 * (3 * n - p)) (by omega) (by omega)
    have e3 : p - 2 * (3 * n - p) = 3 * (p - 2 * n) := by omega
    rw [e3, hmul, h3] at e2
    have e4 := hAE (2 * n) (by omega) (by omega)
    have e5 : f (2 * n) = f 2 * f n := hmul _ _
    rw [h2] at e1 e5
    linarith

theorem geven_three [NeZero p] (hmul : ∀ a b, f (a * b) = f a * f b) (h2 : f 2 = -1)
    (h3 : f 3 = -1) (hp2 : p % 2 = 1) (hAE : AllEqualF f p) (hp3 : p % 3 ≠ 0) (x : ZMod p) :
    evenCompletion p f (3 * x) = -evenCompletion p f x := by
  by_cases hx : x = 0
  · have h := hmul 0 2; rw [zero_mul, h2] at h
    simp [hx, evenCompletion]; linarith
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h]; exact geven_three_nat hmul h2 h3 hp2 hAE hp3 hn hhi
  · rw [h, mul_neg, evenCompletion_neg hp2, evenCompletion_neg hp2,
      geven_three_nat hmul h2 h3 hp2 hAE hp3 hn hhi]

theorem geven_sign [NeZero p] (hsign : ∀ n, 0 < n → f n = 1 ∨ f n = -1) (hp2 : p % 2 = 1)
    {x : ZMod p} (hx : x ≠ 0) :
    evenCompletion p f x = 1 ∨ evenCompletion p f x = -1 := by
  obtain ⟨n, hn, hhi, h | h⟩ := centralRepresentative hp2 hx
  · rw [h, evenCompletion_nat hhi]; exact hsign n hn
  · rw [h, evenCompletion_neg hp2, evenCompletion_nat hhi]; exact hsign n hn

end GeneralEven

/-- A multiplicative `±1` function on `ZMod p` taking the value `-1` somewhere is the Legendre
symbol. -/
theorem eq_legendre_of_mul' {p : ℕ} [Fact p.Prime] (F : ZMod p → ℤ)
    (hmul : ∀ x y : ZMod p, F (x * y) = F x * F y)
    (hsign : ∀ x : ZMod p, x ≠ 0 → F x = 1 ∨ F x = -1)
    {c : ZMod p} (hc : F c = -1) :
    ∀ x : ZMod p, x ≠ 0 → F x = legendreSym p x.val := by
  have hsq : ∀ y : ZMod p, y ≠ 0 → F (y * y) = 1 := by
    intro y hy
    rw [hmul]; rcases hsign y hy with h | h <;> rw [h] <;> norm_num
  have hc0 : c ≠ 0 := by
    rintro rfl
    have := hmul 0 0; rw [mul_zero, hc] at this; norm_num at this
  have hcs : ¬ IsSquare c := by
    rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; exact hc0 hy
    have := hsq y hy0; rw [← hy, hc] at this; norm_num at this
  have hcv : ((c.val : ℤ) : ZMod p) = c := by simp
  have hlc : legendreSym p c.val = -1 := by
    rw [legendreSym.eq_neg_one_iff p]; rw [hcv]; exact hcs
  intro x hx
  have hxv : ((x.val : ℤ) : ZMod p) = x := by simp
  by_cases hxs : IsSquare x
  · obtain ⟨y, hy⟩ := hxs
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; exact hx hy
    have hFx : F x = 1 := by rw [hy]; exact hsq y hy0
    rw [hFx]
    symm
    rw [legendreSym.eq_one_iff p (by rw [hxv]; exact hx)]
    rw [hxv]; exact ⟨y, hy⟩
  · have hl : legendreSym p x.val = -1 := by
      rw [legendreSym.eq_neg_one_iff p]; rw [hxv]; exact hxs
    have hmx : IsSquare (c * x) := by
      have h1 : legendreSym p ((c.val : ℤ) * (x.val : ℤ)) = 1 := by
        rw [legendreSym.mul, hlc, hl]; norm_num
      have hne : (((c.val : ℤ) * (x.val : ℤ) : ℤ) : ZMod p) ≠ 0 := by
        push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; exact mul_ne_zero hc0 hx
      have := (legendreSym.eq_one_iff p hne).mp h1
      push_cast at this; rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
    obtain ⟨y, hy⟩ := hmx
    have hy0 : y ≠ 0 := by
      rintro rfl; simp at hy; rcases hy with h | h; exact hc0 h; exact hx h
    have hfx : F (c * x) = 1 := by rw [hy, hsq y hy0]
    rw [hmul, hc] at hfx
    rw [hl]
    rcases hsign x hx with h | h
    · rw [h] at hfx; norm_num at hfx
    · exact h

/-- **Theorem F, mixed part.** Let `f` be completely multiplicative, `±1` on positive integers,
with `f 2 = f 3 = -1`. If a prime `p ≥ 7` has no `a + b = p` with `f a ≠ f b`, then
`p ≡ 1 (mod 4)` and `f` agrees with the Legendre symbol mod `p` on `(0, p/2)`. -/
theorem legendre_of_no_mixed_pair {f : ℕ → ℤ} (hf1 : f 1 = 1)
    (hsign : ∀ n, 0 < n → f n = 1 ∨ f n = -1)
    (hmul : ∀ a b, f (a * b) = f a * f b) (h2 : f 2 = -1) (h3 : f 3 = -1)
    {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    (hno : ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = p ∧ f a ≠ f b) :
    p % 4 = 1 ∧ ∀ n : ℕ, 0 < n → 2 * n < p → f n = legendreSym p n := by
  have hp : p.Prime := Fact.out
  have hp2 : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hp3 : p % 3 ≠ 0 := by
    intro h
    have := (hp.dvd_iff_eq (by decide : (3 : ℕ) ≠ 1)).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have hAE : AllEqualF f p := by
    intro a ha hap
    by_contra hne
    exact hno ⟨p - a, a, by omega, ha, by omega, hne⟩
  let G := evenCompletion p f
  have hG0 : G 0 = 0 := by
    show f _ = 0
    have h02 := hmul 0 2
    rw [zero_mul, h2] at h02
    simp only [ZMod.valMinAbs_zero, Int.natAbs_zero]
    linarith
  have hG1 : G 1 = 1 := by
    have := evenCompletion_nat (p := p) (n := 1) (f := f) (by omega)
    simpa [G, hf1] using this
  have hGneg : ∀ x, G (-x) = G x := evenCompletion_neg hp2
  have hGtwo : ∀ x, G (2 * x) = -G x := geven_two hmul h2 hp2 hAE
  have hGthree : ∀ x, G (3 * x) = -G x := geven_three hmul h2 h3 hp2 hAE hp3
  have hm1 : G (-1) = 1 := by rw [hGneg, hG1]
  have hG2 : G 2 = -1 := by simpa [hG1] using hGtwo 1
  have hG3 : G 3 = -1 := by simpa [hG1] using hGthree 1
  have hsgn : ∀ x : ZMod p, x ≠ 0 → G x = 1 ∨ G x = -1 := fun x hx => geven_sign hsign hp2 hx
  have hGnz : ∀ x : ZMod p, x ≠ 0 → G x ≠ 0 := by
    intro x hx
    rcases hsgn x hx with h | h <;> omega
  have hminus : IsGood G (-1) := by
    intro x; rw [hm1, one_mul, neg_one_mul, hGneg]
  have htwo : IsGood G 2 := by
    intro x; rw [hG2, hGtwo, neg_one_mul]
  have hthree : IsGood G 3 := by
    intro x; rw [hG3, hGthree, neg_one_mul]
  have hlocal : ∀ a b : ℕ, 0 < a → 0 < b → 2 * (a * b) < p →
      G ((a * b : ℕ) : ZMod p) = G a * G b := by
    intro a b ha hb hab
    have ha' : a ≤ a * b := Nat.le_mul_of_pos_right a hb
    have hb' : b ≤ a * b := Nat.le_mul_of_pos_left b ha
    show evenCompletion p f _ = evenCompletion p f _ * evenCompletion p f _
    rw [evenCompletion_nat hab, evenCompletion_nat (by omega), evenCompletion_nat (by omega), hmul]
  have hmulG := half_interval_extension_via_invariance p hp (by omega) G hG0 hG1 hGnz
    hminus htwo hthree hlocal
  have hleg := eq_legendre_of_mul' G hmulG hsgn hG2
  have h4 : p % 4 = 1 := by
    have hl := hleg (-1) (by simp)
    rw [hm1] at hl
    have hsq : IsSquare (-1 : ZMod p) := by
      have hne : (((-1 : ZMod p).val : ℤ) : ZMod p) ≠ 0 := by simp
      have := (legendreSym.eq_one_iff p hne).mp hl.symm
      simpa using this
    have := ZMod.exists_sq_eq_neg_one_iff.mp hsq
    omega
  refine ⟨h4, fun n hn hhi => ?_⟩
  have hnz : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd; exact absurd (Nat.le_of_dvd hn hd) (by omega)
  have := hleg n hnz
  have e1 : G (n : ZMod p) = f n := evenCompletion_nat hhi
  rw [e1, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
  exact this

end OddCase

