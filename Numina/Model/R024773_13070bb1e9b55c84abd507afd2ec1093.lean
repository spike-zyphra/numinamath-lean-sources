import Mathlib

theorem algebra_290291 (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    x * Real.sqrt (y - 1) + y * Real.sqrt (x - 1) = x * y ↔ x = 2 ∧ y = 2 := by
  constructor
  · -- Assume x * sqrt (y - 1) + y * sqrt (x - 1) = x * y, prove x = 2 ∧ y = 2
    intro h_eq
    have h2 : Real.sqrt (x - 1) ≥ 0 := by positivity
    have h3 : Real.sqrt (y - 1) ≥ 0 := by positivity
    have h4 : (Real.sqrt (x - 1)) ^ 2 = x - 1 := by
      rw [Real.sq_sqrt]
      linarith
    have h5 : (Real.sqrt (y - 1)) ^ 2 = y - 1 := by
      rw [Real.sq_sqrt]
      linarith
    have h6 : (x - 2) ^ 2 + (y - 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (Real.sqrt (x - 1) - 1), sq_nonneg (Real.sqrt (y - 1) - 1), 
        sq_nonneg (x - 2), sq_nonneg (y - 2), 
        Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (y - 1),
        mul_nonneg (Real.sqrt_nonneg (x - 1)) (Real.sqrt_nonneg (y - 1)), 
        Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (y - 1), 
        sq_nonneg (Real.sqrt (x - 1) ^ 2 - (x - 1)), 
        sq_nonneg (Real.sqrt (y - 1) ^ 2 - (y - 1)), 
        h4, h5, 
        Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (y - 1), 
        mul_nonneg (show (0 : ℝ) ≤ x - 1 by nlinarith) (show (0 : ℝ) ≤ y - 1 by nlinarith)
      ]
    have h7 : x - 2 = 0 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), h6]
    have hx2 : x = 2 := by
      linarith
    have h8 : y - 2 = 0 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), h6]
    have hy2 : y = 2 := by
      linarith
    exact ⟨hx2, hy2⟩
  · -- Assume x = 2 ∧ y = 2, prove x * sqrt (y - 1) + y * sqrt (x - 1) = x * y
    rintro ⟨rfl, rfl⟩
    have h1 : Real.sqrt (2 - 1) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1]
    all_goals
      norm_num