import Mathlib

lemma sum_le_length_if_all_mem_le_one {l : List ℕ} (h : ∀a ∈ l, a = 0 ∨ a = 1) : l.sum ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp at h
    obtain ⟨h₁, h₂⟩ := h
    specialize ih h₂
    simp
    obtain (h | h) := h₁
    all_goals {
      rw [h]
      linarith
    }

theorem number_theory_232259 {n : ℕ} (hn : IsLeast {n : ℕ | 0 < n ∧ 72 ∣ n ∧ ∀ d ∈ Nat.digits 10 n, d = 0 ∨ d = 1 } n) : (Nat.digits 10 n).length = 12 := by
  suffices n = 111111111000 by
    rw [this]
    norm_num
  rcases hn with ⟨hn₁, hn₂⟩
  rw [mem_lowerBounds] at hn₂
  apply Nat.le_antisymm
  · specialize hn₂ 111111111000
    apply hn₂
    norm_num
  · suffices ∀ x ∈ {n : ℕ | 0 < n ∧ 72 ∣ n ∧ ∀ d ∈ Nat.digits 10 n, d = 0 ∨ d = 1}, 111111111000 ≤ x by
      apply this
      assumption
    intro x hx
    simp at hx
    rcases hx with ⟨hx₀, hx₁, hx₂⟩
    have hx₃ : 1000 ∣ x := by
      have hx₃ : 8 ∣ x := by
        apply Nat.dvd_trans ?_ hx₁
        norm_num
      obtain ⟨r, hr₁⟩ := show ∃r, r = x % 1000 by simp
      have hr₂ : ∀b ∈ (Nat.digits 10 r), b = 0 ∨ b = 1 := by
        intro b hb₁
        by_cases hr₂: r = 0
        · have : (Nat.digits 10 r) = [] := by
            rw [hr₂]
            simp
          rw [this] at hb₁
          simp at hb₁
        by_cases hx₄: x < 1000
        · rw [show r = x by omega] at hb₁
          exact hx₂ b hb₁
        push_neg at hx₄
        have hb₂ : b ∈ (Nat.digits 10 x) := by
          have : 4 ≤ ((Nat.digits 10 x)).length := by
            rw [Nat.digits_len _ _ (by norm_num) (by linarith)]; simp
            exact Nat.le_log_of_pow_le (by norm_num) hx₄
          rw [Nat.digits_eq_cons_digits_div (by norm_num) hr₂] at hb₁
          rw [Nat.digits_eq_cons_digits_div (by norm_num) (by linarith)]
          simp at hb₁ ⊢
          obtain (hb | hb) := hb₁
          · apply Or.inl
            rw [show x % 10 = r % 10 by omega]
            exact hb
          · apply Or.inr
            by_cases hr₃: r < 10
            · rw [Nat.div_eq_of_lt hr₃] at hb
              simp at hb
            rw [Nat.digits_eq_cons_digits_div (by norm_num) (by omega)] at hb ⊢
            simp at hb hr₃ ⊢
            obtain (hb | hb) := hb
            · apply Or.inl
              rw [hb]
              apply Nat.mod_eq_of_modEq ?_ (by omega)
              rw [hr₁, show (1000 = 10 * 10 * 10) by norm_num, Nat.mod_mul_left_div_self, Nat.ModEq]
              omega
            · apply Or.inr
              by_cases hr₄: r < 100
              · rw [show r / 10 / 10 = 0 by omega] at hb
                simp at hb
              rw [Nat.digits_eq_cons_digits_div (by norm_num) (by omega)] at hb ⊢
              simp at hb hr₄ ⊢
              obtain (hb | hb) := hb
              · apply Or.inl
                rw [hb]
                apply Nat.mod_eq_of_modEq ?_ (by omega)
                rw [hr₁, show (1000 = 10 * 10 * 10) by norm_num, Nat.mod_mul_left_div_self, Nat.mod_mul_left_div_self]
              · rw [show r / 10 / 10 / 10 = 0 by omega] at hb
                simp at hb
        exact hx₂ b hb₂
      apply Nat.dvd_of_mod_eq_zero
      rw [←hr₁]
      have hr₃ : r < 1000 := by omega
      have hr₄ : 8 ∣ r := by rw [hr₁]; omega
      by_contra! hr₅
      rw [Nat.digits_eq_cons_digits_div (by norm_num) hr₅] at hr₂
      simp at hr₂
      obtain ⟨(hl₁ | hl₁), hr₂⟩ := hr₂
      · by_cases hr₆: r / 10 ≠ 0
        · rw [Nat.digits_eq_cons_digits_div (by norm_num) hr₆] at hr₂
          simp at hr₂
          obtain ⟨(hl₂ | hl₂), hr₂⟩ := hr₂
          · obtain (rfl | rfl | rfl | rfl) := show r = 200 ∨ r = 400 ∨ r = 600 ∨ r = 800 by omega
            all_goals norm_num at hr₂
          · omega
        omega
      · omega
    have hx₄ : 9 ∣ (Nat.digits 10 x).sum := by
      apply (Nat.nine_dvd_iff x).mp
      apply Nat.dvd_trans (by norm_num) hx₁
    obtain ⟨m, hm₁⟩ := hx₃
    have hx₃ : Nat.digits 10 x = 0 :: 0 :: 0 :: (Nat.digits 10 m) := by
      rw [hm₁, Nat.digits_eq_cons_digits_div (by norm_num) (by linarith)]
      rw [Nat.digits_eq_cons_digits_div (by norm_num) (by omega)]
      rw [Nat.digits_eq_cons_digits_div (by norm_num) (by omega)]
      simp
      repeat use (by omega)
    rw [hx₃] at hx₂ hx₄
    norm_num at hx₂ hx₄
    have hm₂ : 9 ≤ (Nat.digits 10 m).sum := by
      obtain ⟨k, hk⟩ := hx₄
      have : (Nat.digits 10 m).sum ≠ 0 := by
        apply Nat.ne_zero_iff_zero_lt.mpr
        have (l : List ℕ) : 0 < l.sum ↔ ∃ x ∈ l, 0 < x := by
          induction l with
          | nil => simp
          | cons x xs ih =>
            simp [← ih]
        rw [this]
        use (Nat.digits 10 m).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr (by linarith))
        use (by apply List.getLast_mem)
        apply Nat.zero_lt_of_ne_zero
        apply Nat.getLast_digit_ne_zero
        linarith
      omega
    suffices 111111111 ≤ m by omega
    by_contra! hm₃
    have hm₄ : (Nat.digits 10 m).length ≤ (Nat.digits 10 111111111).length := by
      apply Nat.le_digits_len_le 10 m 111111111
      linarith
    simp at hm₄
    have hm₅ : (Nat.digits 10 m).sum ≤ (Nat.digits 10 m).length := by
      apply sum_le_length_if_all_mem_le_one
      assumption
    have hm₆ : (Nat.digits 10 m).length = 9 := by omega
    have hm₇ : (Nat.digits 10 m).sum = 9 := by omega
    have hm₈ : m = 111111111 := by
      obtain ⟨l, hl⟩ := show ∃l, l = Nat.digits 10 m by simp
      rw [←hl] at hm₆ hm₇ hx₂
      have hl₁ : ∀a ∈ l, a ≤ 1 := by
        intro a ha
        specialize hx₂ a ha
        omega
      let [a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉] := l
      simp at hl₁ hm₆ hm₇
      rw [←Nat.ofDigits_digits 10 111111111]
      simp
      suffices Nat.digits 10 m = [1, 1, 1, 1, 1, 1, 1, 1, 1] by
        rw [←this]
        exact Eq.symm (Nat.ofDigits_digits 10 m)
      rw [←hl]; simp
      omega
    linarith
