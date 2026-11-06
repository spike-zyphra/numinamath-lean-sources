import Mathlib

open Real Set

theorem inequalities_30536 (a b : ℝ) (ha : a ∈ Icc 0 (π/2)) (hb : b ∈ Icc 0 (π/2)) :
    sin a ^ 6 + 3 * sin a ^ 2 * cos b ^ 2 + cos b ^ 6 = 1 ↔ a = b := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with  ⟨hb1, hb2⟩
  constructor
  · -- Assume sin a^6 + 3 * sin a ^ 2 * cos b ^ 2 + cos b^6 =1, prove a =b
    intro h
    have h1 : sin a ≥ 0 := by apply sin_nonneg_of_nonneg_of_le_pi; linarith [Real.pi_pos]; linarith [Real.pi_pos]
    have h2 : cos a ≥ 0 := by apply cos_nonneg_of_mem_Icc; constructor; all_goals linarith [Real.pi_pos]
    have h3 : sin b ≥ 0 := by apply sin_nonneg_of_nonneg_of_le_pi; linarith [Real.pi_pos]; linarith [Real.pi_pos]
    have h4 : cos b ≥ 0 := by apply cos_nonneg_of_mem_Icc; constructor; all_goals linarith [Real.pi_pos]
    have h5 : sin a ^ 2 + cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
    have h6 : sin b ^ 2 + cos b ^ 2 = 1 := Real.sin_sq_add_cos_sq b
    have h7 : sin a ^ 6 + 3 * sin a ^ 2 * cos b ^ 2 + cos b ^ 6 = 1 := h
    have h8 : (sin a ^ 2 + cos b ^ 2 - 1) * (sin a ^ 4 + cos b ^ 4 + 1 - 3 * sin a ^ 2 * cos b ^ 2) = 0 := by
      nlinarith [sq_nonneg (sin a ^ 2 - cos b ^ 2), sq_nonneg (sin a ^ 2 + cos b ^ 2 - 1), sq_nonneg (sin a ^ 2 - 1), sq_nonneg (cos b ^ 2 - 1)]
    cases' (mul_eq_zero.1 h8) with h9 h10
    · -- Case where h9 is true
      have h10 : sin a ^ 2 + cos b ^ 2 = 1 := by linarith
      have h11 : sin a ^ 2 = sin b ^ 2 := by nlinarith [h10, h6]
      have h12 : sin a = sin b := by nlinarith [h11, h1, h3]
      have h13 : a = b := by
        by_cases h20 : a < b
        · -- Assume a < b
          have h21 : sin a < sin b := by
            apply sin_lt_sin_of_lt_of_le_pi_div_two
            all_goals linarith
          linarith [h12, h21]
        by_cases h23 : b < a
        · -- Assume b < a
          have h24 : sin b < sin a := by
            apply sin_lt_sin_of_lt_of_le_pi_div_two
            all_goals linarith
          linarith [h12, h24]
        linarith
      exact h13
    · -- Case where h10 is true
      have h11 : sin a ^ 4 + cos b ^ 4 + 1 - 3 * sin a ^ 2 * cos b ^ 2 = 0 := by nlinarith
      have h12 : sin a ^ 2 = cos b ^ 2 := by
        nlinarith [sq_nonneg (sin a ^ 2 - cos b ^ 2), sq_nonneg (sin a ^ 2 + cos b ^ 2 - 1), sq_nonneg (sin a - cos b), sq_nonneg (sin a - sin b), sq_nonneg (cos b - sin b)]
      have h13 : sin a = cos b := by
        nlinarith [h12, h1, h4]
      have h17 : a = b := by
        have h18 : (a - b) ^ 2 = 0 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (sin a - cos b), sq_nonneg (sin a ^ 2 - cos b ^ 2), sq_nonneg (a - (Real.pi / 2 - b)), sq_nonneg (a + b - Real.pi / 2)]
        have h19 : a - b = 0 := by
          nlinarith
        linarith
      exact h17
  · -- Assume a = b, prove sin a ^ 6 + 3 * sin a ^ 2 * cos b ^ 2 + cos b ^ 6 = 1
    intro h
    rw [show b = a by linarith [h]]
    have h1 : sin a ^ 2 + cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
    nlinarith [sq_nonneg (sin a ^ 2 - cos a ^ 2), sq_nonneg (sin a ^ 2 + cos a ^ 2 - 1)]