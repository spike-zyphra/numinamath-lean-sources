import Mathlib
/-Find all integrals a,b,c such that
a^2 = b * c + 1 ∧ b^2 = c * a + 1
-/
theorem algebra_123343 (a b c : ℤ) :
    a^2 = b * c + 1 ∧ b^2 = c * a + 1 ↔
    (a = 1 ∧ b = 1 ∧ c = 0) ∨
    (a = -1 ∧ b = -1 ∧ c = 0) ∨
    (a = 1 ∧ b = -1 ∧ c = 0) ∨
    (a = -1 ∧ b = 1 ∧ c = 0) ∨
    (a = 1 ∧ b = 0 ∧ c = -1) ∨
    (a = -1 ∧ b = 0 ∧ c = 1) ∨
    (a = 0 ∧ b = 1 ∧ c = -1) ∨
    (a = 0 ∧ b = -1 ∧ c = 1) := by

  constructor
  · -- Forward direction: prove that if a^2 = bc + 1 and b^2 = ca + 1, then one of the 8 cases holds
    rintro ⟨h1, h2⟩
    have h_sub : a^2 - b^2 = b * c - c * a := by linarith
    have h_factor : (a - b) * (a + b) = c * (b - a) := by nlinarith [h_sub]
    have h_zero : (a - b) * (a + b + c) = 0 := by
      nlinarith [h_factor]
    cases (mul_eq_zero.mp h_zero) with
    | inl h_eq =>
      have hb : b = a := by linarith
      rw [hb] at h1 h2
      have h_eq1 : a * (a - c) = 1 := by nlinarith [h1]
      have h_a : a = 1 ∨ a = -1 := by
        have h : a * (a - c) = 1 := h_eq1
        have h1 : a = 1 ∨ a = -1 := by
          have h2 : a * (a - c) = 1 := h
          have h3 : a = 1 ∨ a = -1 := by
            apply Int.eq_one_or_neg_one_of_mul_eq_one
            exact h2
          exact h3
        exact h1
      cases h_a with
      | inl ha1 =>
        have hc : c = 0 := by
          rw [ha1] at h_eq1
          have : (1 : ℤ) * (1 - c) = 1 := by linarith
          have : 1 - c = 1 := by
            have h : (1 : ℤ) * (1 - c) = 1 := by linarith
            omega
          linarith
        left
        exact ⟨ha1, by linarith, hc⟩
      | inr ha_neg1 =>
        have hc : c = 0 := by
          rw [ha_neg1] at h_eq1
          have : (-1 : ℤ) * (-1 - c) = 1 := by linarith
          have : -1 - c = -1 := by
            have h : (-1 : ℤ) * (-1 - c) = 1 := by linarith
            omega
          linarith
        right
        left
        exact ⟨ha_neg1, by linarith, hc⟩
    | inr h_sum =>
      have hc : c = -a - b := by linarith
      rw [hc] at h1
      have h_eq : a^2 + a * b + b^2 = 1 := by nlinarith
      have h_a : a ≤ 1 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), h_eq]
      have h_b : b ≤ 1 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), h_eq]
      have h_a_lower : -1 ≤ a := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), h_eq]
      have h_b_lower : -1 ≤ b := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), h_eq]
      interval_cases a <;> interval_cases b <;> omega
  · -- Backward direction: prove that each of the 8 cases implies a^2 = bc + 1 and b^2 = ca + 1
    rintro (h | h | h | h | h | h | h | h)
    · rcases h with ⟨ha, hb, hc⟩
      constructor
      · -- Show a^2 = b * c + 1
        rw [ha, hb, hc]
        norm_num
      · -- Show b^2 = c * a + 1
        rw [hb, hc, ha]
        norm_num
    · rcases h with ⟨ha, hb, hc⟩
      constructor
      · -- Show a^2 = b * c + 1
        rw [ha, hb, hc]
        norm_num
      · -- Show b^2 = c * a + 1
        rw [hb, hc, ha]
        norm_num
    · rcases h with ⟨ha, hb, hc⟩
      constructor
      · -- Show a^2 = b * c + 1
        rw [ha, hb, hc]
        norm_num
      · -- Show b^2 = c * a + 1
        rw [hb, hc, ha]
        norm_num
    · rcases h with ⟨ha, hb, hc⟩
      constructor
      · -- Show a^2 = b * c + 1
        rw [ha, hb, hc]
        norm_num
      · -- Show b^2 = c * a + 1
        rw [hb, hc, ha]
        norm_num
    · rcases h with ⟨ha, hb, hc⟩
      constructor
      · -- Show a^2 = b * c + 1
        rw [ha, hb, hc]
        norm_num
      · -- Show b^2 = c * a + 1
        rw [hb, hc, ha]
        norm_num
    · rcases h with ⟨ha, hb, hc⟩
      constructor
      · -- Show a^2 = b * c + 1
        rw [ha, hb, hc]
        norm_num
      · -- Show b^2 = c * a + 1
        rw [hb, hc, ha]
        norm_num
    · rcases h with ⟨ha, hb, hc⟩
      constructor
      · -- Show a^2 = b * c + 1
        rw [ha, hb, hc]
        norm_num
      · -- Show b^2 = c * a + 1
        rw [hb, hc, ha]
        norm_num
    · rcases h with ⟨ha, hb, hc⟩
      constructor
      · -- Show a^2 = b * c + 1
        rw [ha, hb, hc]
        norm_num
      · -- Show b^2 = c * a + 1
        rw [hb, hc, ha]
        norm_num