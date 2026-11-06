import Mathlib

theorem inequalities_3541 (a b : ℝ) (h₀ : a + b ≠ 0) :
  a^2 + b^2 + (a * b + 1) ^ 2 / (a + b) ^ 2 ≥ 2 := by

  have h1 : a^2 + b^2 + (a * b + 1) ^ 2 / (a + b) ^ 2 - 2 ≥ 0 := by

    have h2 : (a^2 + b^2 + (a * b + 1) ^ 2 / (a + b) ^ 2 - 2) = ((a^2 + b^2) * (a + b) ^ 2 + (a * b + 1) ^ 2 - 2 * (a + b) ^ 2) / ( (a + b) ^ 2 ) := by 
      field_simp
      <;> ring

    rw [h2]

    apply div_nonneg

    have h3 : (a ^ 2 + b ^ 2) * (a + b) ^ 2 + (a * b + 1) ^ 2 - 2 * (a + b) ^ 2 = ((a + b) ^ 2 - (a * b + 1)) ^ 2 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - (a * b + 1) / (a + b)), sq_nonneg (a * b - 1), sq_nonneg (a - b)]

    have h4 : ((a ^ 2 + b ^ 2) * (a + b) ^ 2 + (a * b + 1) ^ 2 - 2 * (a + b) ^ 2) ≥ 0 := by 
      rw [h3]
      apply sq_nonneg

    linarith

    all_goals
      have h4 : (a + b) ^ 2 > 0 := by 
        apply pow_two_pos_of_ne_zero 
        exact h₀ 
      nlinarith

  linarith [h1]