import Mathlib

theorem algebra_279974 (x y : ℝ) (h : x^2 - x * y + y^2 = 1) :
    x + 2 * y ≤ 2 * Real.sqrt 21 / 3 := by 
  have h2 : (x + 2 * y) ^ 2 ≤ (28 / 3 : ℝ) := by
    nlinarith [sq_nonneg (x - 4 / 5 * y), sq_nonneg (y + 2 / 5 * x), sq_nonneg (x - 2 * y), sq_nonneg (x + 4 * y), sq_nonneg (x - 4 * y / 5), sq_nonneg (y + 2 * x / 5), sq_nonneg (x + 2 * y - 4 * Real.sqrt 21 / 21 * (x + 2 * y)), sq_nonneg (x - 4 * y / 5), sq_nonneg (y - 5 * x / 4), sq_nonneg (x + 4 * y / 3), sq_nonneg (y - (5 * x)/4), sq_nonneg (x * y)]
  
  have h3 : x + 2 * y ≤ 2 * Real.sqrt 21 / 3 := by 
    have h4 : (x + 2 * y) ≤ Real.sqrt (28 / 3 : ℝ) := by 
      have h5 : (x + 2 * y) ^ 2 ≤ (28 / 3 : ℝ) := h2
      have h6 : (x + 2 * y) ≤ Real.sqrt (28 / 3 : ℝ) := by
        apply Real.le_sqrt_of_sq_le
        linarith 
      linarith

    have h7 : Real.sqrt (28 / 3 : ℝ) = 2 * Real.sqrt 21 / 3 := by 
      have h8 : Real.sqrt (28 / 3 : ℝ) ≥ 0 := Real.sqrt_nonneg (28 / 3 : ℝ)
      have h9 : (2 * Real.sqrt 21 / 3 : ℝ) ≥ 0 := by 
        have h9 : Real.sqrt (21 : ℝ) ≥ 0 := Real.sqrt_nonneg 21
        linarith 
      have h10 : Real.sqrt (28 / 3 : ℝ) ^ 2 = (2 * Real.sqrt 21 / 3 : ℝ) ^ 2 := by 
        have h11 : Real.sqrt (28 / 3 : ℝ) ^ 2 = (28 / 3 : ℝ) := by 
          rw [Real.sq_sqrt] 
          all_goals 
            nlinarith 
        have h12 : (2 * Real.sqrt 21 / 3 : ℝ) ^ 2 = (28 / 3 : ℝ) := by 
          nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by nlinarith)]
        nlinarith 
      have h11 : Real.sqrt (28 / 3 : ℝ) = (2 * Real.sqrt 21 / 3 : ℝ) := by 
        nlinarith [h10, Real.sqrt_nonneg (28 / 3 : ℝ), Real.sqrt_nonneg 21]
      linarith 
    nlinarith [h4, h7, Real.sqrt_nonneg 21]

  exact h3