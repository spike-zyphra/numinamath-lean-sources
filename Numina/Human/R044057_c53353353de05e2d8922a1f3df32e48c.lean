import Mathlib

theorem number_theory_168968 :
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ c ∣ a * b + 1 ∧ a ∣ b * c + 1 ∧ b ∣ c * a + 1} = {(1, 1, 1), (2, 1, 1), (1, 2, 1), (1, 1, 2), (2, 1, 3), (2, 3, 1), (3, 2, 1), (1, 2, 3), (1, 3, 2), (3, 1, 2), (2, 7, 3), (2, 3, 7), (3, 2, 7), (7, 2, 3), (7, 3, 2), (3, 7, 2)} := by
  ext ⟨a, b, c⟩
  apply Iff.intro
  . rintro ⟨ha, hb, hc, h₀, h₁, h₂⟩
    have hlm₀ (a b c : ℕ)
        (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h₀ : c ∣ a * b + 1)
        (h₁ : a ∣ b * c + 1) (h₂ : b ∣ c * a + 1) :
        Nat.Coprime a b := by
      let m := Nat.gcd a b
      have hm : m ∣ 1 := by
        unfold m
        rw [@Nat.dvd_add_iff_right _ (c * a)]
        . calc
            _ ∣ b := Nat.gcd_dvd_right a b
            _ ∣ c * a + 1 := h₂
        . calc
            _ ∣ a := Nat.gcd_dvd_left a b
            _ ∣ c * a := Nat.dvd_mul_left a c
      simp [m] at hm
      exact Nat.coprime_iff_gcd_eq_one.mpr hm
    have h₃ : a * b * c ∣ a * b + b * c + c * a + 1 := by
      have h₃ : Nat.Coprime (a * b) c := by
        apply Nat.Coprime.mul
        . apply Nat.Coprime.symm
          apply hlm₀ c a b hc ha hb h₂ h₀ h₁
        . apply hlm₀ b c a hb hc ha h₁ h₂ h₀
      have h₄ : Nat.Coprime a b := by
        apply hlm₀ a b c ha hb hc h₀ h₁ h₂
      iterate 2 apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (by assumption)
      . rw [show a * b + b * c + c * a + 1 = a * (b + c) + (b * c + 1) by ring, <-Nat.dvd_add_iff_left]
        . apply Nat.dvd_mul_right
        . exact h₁
      . rw [show a * b + b * c + c * a + 1 = b * (c + a) + (c * a + 1) by ring, <-Nat.dvd_add_iff_left]
        . apply Nat.dvd_mul_right
        . exact h₂
      . rw [show a * b + b * c + c * a + 1 = c * (a + b) + (a * b + 1) by ring, <-Nat.dvd_add_iff_left]
        . apply Nat.dvd_mul_right
        . exact h₀
    simp
    by_contra hsol
    have hlm₁ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h₀ : c ∣ a * b + 1)
        (h₁ : a ∣ b * c + 1) (h₂ : b ∣ c * a + 1) (h₃ : a * b * c ∣ a * b + b * c + c * a + 1)
        (hsol : ¬(a = 1 ∧ b = 1 ∧ c = 1 ∨ a = 2 ∧ b = 1 ∧ c = 1 ∨ a = 1 ∧ b = 2 ∧ c = 1 ∨ a = 1 ∧ b = 1 ∧ c = 2 ∨ a = 2 ∧ b = 1 ∧ c = 3 ∨ a = 2 ∧ b = 3 ∧ c = 1 ∨ a = 3 ∧ b = 2 ∧ c = 1 ∨ a = 1 ∧ b = 2 ∧ c = 3 ∨ a = 1 ∧ b = 3 ∧ c = 2 ∨ a = 3 ∧ b = 1 ∧ c = 2 ∨ a = 2 ∧ b = 7 ∧ c = 3 ∨ a = 2 ∧ b = 3 ∧ c = 7 ∨ a = 3 ∧ b = 2 ∧ c = 7 ∨ a = 7 ∧ b = 2 ∧ c = 3 ∨ a = 7 ∧ b = 3 ∧ c = 2 ∨ a = 3 ∧ b = 7 ∧ c = 2))
        (ha' : a ≤ 2) : b ≥ 5 := by
      by_contra! h₅
      interval_cases b
      . interval_cases a
        . apply Nat.Prime.eq_one_or_self_of_dvd (Nat.prime_two) at h₀
          rcases h₀ with (h₀ | h₀)
          all_goals
            subst c
            tauto
        . apply Nat.Prime.eq_one_or_self_of_dvd (Nat.prime_three) at h₀
          rcases h₀ with (h₀ | h₀)
          all_goals
            subst c
            tauto
      . interval_cases a
        . apply Nat.Prime.eq_one_or_self_of_dvd (Nat.prime_three) at h₀
          rcases h₀ with (h₀ | h₀)
          all_goals
            subst c
            tauto
        . omega
      . interval_cases a
        . apply Nat.le_of_dvd (by omega) at h₀
          apply Nat.le_of_dvd (by omega) at h₂
          simp at h₀ h₂
          interval_cases c
          . tauto
          . omega
          . omega
        . apply Nat.Prime.eq_one_or_self_of_dvd (by decide) at h₀
          rcases h₀ with (h₀ | h₀)
          all_goals
            subst c
            tauto
      . interval_cases a
        . apply Nat.Prime.eq_one_or_self_of_dvd (Nat.prime_five) at h₀
          omega
        . omega
    clear hlm₀
    have hlm₂ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h₀ : c ∣ a * b + 1)
        (h₁ : a ∣ b * c + 1) (h₂ : b ∣ c * a + 1) (h₃ : a * b * c ∣ a * b + b * c + c * a + 1)
        (hsol : ¬(a = 1 ∧ b = 1 ∧ c = 1 ∨ a = 2 ∧ b = 1 ∧ c = 1 ∨ a = 1 ∧ b = 2 ∧ c = 1 ∨ a = 1 ∧ b = 1 ∧ c = 2 ∨ a = 2 ∧ b = 1 ∧ c = 3 ∨ a = 2 ∧ b = 3 ∧ c = 1 ∨ a = 3 ∧ b = 2 ∧ c = 1 ∨ a = 1 ∧ b = 2 ∧ c = 3 ∨ a = 1 ∧ b = 3 ∧ c = 2 ∨ a = 3 ∧ b = 1 ∧ c = 2 ∨ a = 2 ∧ b = 7 ∧ c = 3 ∨ a = 2 ∧ b = 3 ∧ c = 7 ∨ a = 3 ∧ b = 2 ∧ c = 7 ∨ a = 7 ∧ b = 2 ∧ c = 3 ∨ a = 7 ∧ b = 3 ∧ c = 2 ∨ a = 3 ∧ b = 7 ∧ c = 2))
        (ha' : a ≤ 2) : False := by
      have h₅ : b ≥ 5 := by
        apply hlm₁ a b c ha hb hc h₀ h₁ h₂ h₃ hsol ha'
      have h₄ : c ≥ 5 := by
        apply hlm₁ a c b ha hc hb _ _ _ _ _ ha'
        . ring_nf at h₂ ⊢
          exact h₂
        . ring_nf at h₁ ⊢
          exact h₁
        . ring_nf at h₀ ⊢
          exact h₀
        . ring_nf at h₃ ⊢
          exact h₃
        . contrapose! hsol
          revert hsol
          rintro (⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩)
          <;> simp [ha, hb, hc]
      interval_cases a
      . rw [show 1 * b + b * c + c * 1 + 1 = (b + c + 1) + b * c by ring, one_mul] at h₃
        rw [<-Nat.dvd_add_iff_left] at h₃
        . apply Nat.le_of_dvd (by omega) at h₃
          nlinarith
        . rfl
      . obtain ⟨m, h₃⟩ := h₃
        suffices (1 / 2 + 1 / b + 1 / c + 1 / (2 * b * c) : ℚ) < 1 by
          field_simp at this
          rw [div_lt_iff₀ (by positivity)] at this
          norm_cast at this
          have hm : m < 1 := by
            nlinarith only [h₃, this]
          simp [show m = 0 by omega] at h₃
        calc
          _ ≤ (1 / 2 + 1 / 5 + 1 / 5 + 1 / 50 : ℚ) := by
            iterate 3 apply add_le_add
            . rfl
            . rw [one_div_le_one_div (by positivity) (by norm_num)]
              simp [h₅]
            . rw [one_div_le_one_div (by positivity) (by norm_num)]
              simp [h₄]
            . rw [one_div_le_one_div (by positivity) (by norm_num)]
              norm_cast
              nlinarith
          _ < 1 := by
            norm_num
    clear hlm₁
    have h₄ : ¬(a ≤ 2 ∨ b ≤ 2 ∨ c ≤ 2) := by
      by_contra! h₄
      rcases h₄ with (ha' | hb' | hc')
      . apply hlm₂ a b c ha hb hc h₀ h₁ h₂ h₃ hsol ha'
      . apply hlm₂ b c a hb hc ha h₁ h₂ h₀ _ _ hb'
        . ring_nf at h₃ ⊢
          exact h₃
        . contrapose! hsol
          revert hsol
          rintro (⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩)
          <;> simp [ha, hb, hc]
      . apply hlm₂ c a b hc ha hb h₂ h₀ h₁ _ _ hc'
        . ring_nf at h₃ ⊢
          exact h₃
        . contrapose! hsol
          revert hsol
          rintro (⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩)
          <;> simp [ha, hb, hc]
    replace h₄ : a ≥ 3 ∧ b ≥ 3 ∧ c ≥ 3 := by
      omega
    have h₅ : ¬(a = 3 ∧ b = 3 ∧ c = 3) := by
      by_contra! h₅
      obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩ := h₅
      norm_num at h₃
    iterate 2 rw [Classical.not_and_iff_or_not_not] at h₅
    have hlm₃ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h₀ : c ∣ a * b + 1) (h₁ : a ∣ b * c + 1) (h₂ : b ∣ c * a + 1) (h₃ : a * b * c ∣ a * b + b * c + c * a + 1) (hsol : ¬(a = 1 ∧ b = 1 ∧ c = 1 ∨ a = 2 ∧ b = 1 ∧ c = 1 ∨ a = 1 ∧ b = 2 ∧ c = 1 ∨ a = 1 ∧ b = 1 ∧ c = 2 ∨ a = 2 ∧ b = 1 ∧ c = 3 ∨ a = 2 ∧ b = 3 ∧ c = 1 ∨ a = 3 ∧ b = 2 ∧ c = 1 ∨ a = 1 ∧ b = 2 ∧ c = 3 ∨ a = 1 ∧ b = 3 ∧ c = 2 ∨ a = 3 ∧ b = 1 ∧ c = 2 ∨ a = 2 ∧ b = 7 ∧ c = 3 ∨ a = 2 ∧ b = 3 ∧ c = 7 ∨ a = 3 ∧ b = 2 ∧ c = 7 ∨ a = 7 ∧ b = 2 ∧ c = 3 ∨ a = 7 ∧ b = 3 ∧ c = 2 ∨ a = 3 ∧ b = 7 ∧ c = 2)) (h₄ : a ≥ 3 ∧ b ≥ 3 ∧ c ≥ 3) (ha' : a ≠ 3) : False := by
      apply Nat.le_of_dvd (by positivity) at h₃
      have h₅ : 3 * (b * c + 1) < a * b * c := by
        calc
          _ < 3 * (b * c) + b * c := by
            simp [Nat.mul_add]
            nlinarith
          _ = 4 * (b * c) := by ring
          _ ≤ a * b * c := by
            rw [mul_assoc]
            apply Nat.mul_le_mul_right _ (by omega)
      have h₆ : 3 * (a * b) ≤ a * b * c := by
        calc
          _ ≤ c * (a * b) := by
            apply Nat.mul_le_mul_right _ (h₄.2.2)
          _ = a * b * c := by ac_rfl
      have h₇ : 3 * (c * a) ≤ a * b * c := by
        calc
          _ ≤ b * (c * a) := by
            apply Nat.mul_le_mul_right _ (h₄.2.1)
          _ = a * b * c := by ac_rfl
      linarith
    rcases h₅ with (ha' | hb' | hc')
    . apply hlm₃ a b c ha hb hc h₀ h₁ h₂ h₃ hsol h₄ ha'
    . apply hlm₃ b c a hb hc ha h₁ h₂ h₀ _ _ (by tauto) hb'
      . ring_nf at h₃ ⊢
        exact h₃
      . contrapose! hsol
        revert hsol
        rintro (⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩)
        <;> simp [ha, hb, hc]
    . apply hlm₃ c a b hc ha hb h₂ h₀ h₁ _ _ (by tauto) hc'
      . ring_nf at h₃ ⊢
        exact h₃
      . contrapose! hsol
        revert hsol
        rintro (⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩)
        <;> simp [ha, hb, hc]
  . rintro (⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩)
    <;> norm_num
