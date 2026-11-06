import Mathlib

theorem algebra_222189 (x : ℝ) (hx : x ≠ 1) : x^2 + (x / (x - 1))^2 = 8 ↔
    x = 2 ∨ x = -1 - Real.sqrt 3 ∨ x = -1 + Real.sqrt 3 := by
  constructor
  · -- Assume x^2 + (x / (x - 1))^2 = 8, prove the disjunction of the three roots
    intro h
    have h1 : x - 1 ≠ 0 := by
      intro h2
      apply hx
      linarith
    -- Convert the equation to polynomial form by multiplying through by (x - 1)^2:
    have eq1 : x ^ 2 + (x / (x - 1)) ^ 2 = 8 := h
    have eq2 : x^2 * (x - 1)^2 + x^2 = 8 * (x - 1)^2 := by
      have eq3 : (x / (x - 1)) ^ 2 = x^2 / (x - 1)^2 := by
        field_simp [h1]
        <;> nlinarith
      rw [eq3] at eq1
      field_simp [h1] at eq1 ⊢
      <;> nlinarith [sq_pos_of_ne_zero (show (x - 1) ≠ 0 by assumption)]
    -- Now that we have a polynomial equation, factor it:
    have eq3 : (x - 2) ^ 2 * (x ^ 2 + 2 * x - 2) = 0 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 2), sq_pos_of_ne_zero (show (x - 1 : ℝ) ≠ 0 by assumption)]
    -- Each factor must be zero:
    cases (mul_eq_zero.1 eq3) with
    | inl h4 =>
      have h5 : (x - 2) ^ 2 = 0 := by
        linarith
      have h6 : x - 2 = 0 := by
        apply pow_eq_zero 
        exact h5
      left
      linarith
    | inr h5 =>
      have h6 : x^2 + 2 * x - 2 = 0 := by linarith
      have h7 : (x - (-1 - Real.sqrt 3)) * (x - (-1 + Real.sqrt 3)) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), sq_nonneg (x + 1 - Real.sqrt 3), sq_nonneg (x + 1 + Real.sqrt 3), h6]
      cases (mul_eq_zero.1 h7) with
      | inl h8 =>
        have h88 : x = -1 - Real.sqrt 3 := by
          linarith
        right
        left
        linarith
      | inr h8 => 
        have h88 : x = -1 + Real.sqrt 3 := by
          linarith
        right
        right
        linarith
  · -- Assume the disjunction of the three roots, prove x^2 + (x / (x - 1))^2 = 8
    rintro (h | h | h)
    · -- If x = 2
      rw [h]
      norm_num
    · -- If x = -1 - Real.sqrt 3
      rw [h]
      have h1 : Real.sqrt 3 > 0 := by
        positivity
      have h4 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have h8 : ( -1 - Real.sqrt 3 : ℝ ) -1 ≠ 0 := by 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3) by linarith)]
      field_simp [h8]
      nlinarith [sq_nonneg (Real.sqrt 3), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), sq_pos_of_pos (show (0 : ℝ) < Real.sqrt 3 by nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)])]
    · -- If x = -1 + Real.sqrt 3
      rw [h]
      have h1 : Real.sqrt 3 > 0 := by
        positivity
      have h4 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have h8 : (-1 + Real.sqrt 3 : ℝ ) -1 ≠ 0 := by 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3) by linarith)]
      field_simp [h8]
      nlinarith [sq_nonneg (Real.sqrt 3), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), sq_pos_of_pos (show (0 : ℝ) < Real.sqrt 3 by nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)])]