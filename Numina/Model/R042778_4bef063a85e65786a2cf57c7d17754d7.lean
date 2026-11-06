import Mathlib

theorem algebra_309249 {x y : ℝ} (hx : x^2 + 1 ≥ 0) (hy : y^2 + 1 ≥ 0)
    (h : (x + Real.sqrt (x^2 + 1)) * (y + Real.sqrt (y^2 + 1)) = 1) :
    x + y = 0 := by

  have h1 : x + Real.sqrt (x^2 + 1) > 0 := by
    have h2 : Real.sqrt (x^2 + 1) > 0 := by
      apply Real.sqrt_pos.2
      nlinarith
    have h3 : Real.sqrt (x^2 + 1) > abs x := by
      cases' abs_cases x with h4 h4
      · -- x ≥ 0
        nlinarith [Real.sqrt_nonneg (x^2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ x^2 + 1 by nlinarith)]
      · -- x < 0
        nlinarith [Real.sqrt_nonneg (x^2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ x^2 + 1 by nlinarith)]
    cases' abs_cases x with h4 h4
    · -- x ≥ 0
      linarith
    · -- x < 0
      linarith

  have h2 : y + Real.sqrt (y^2 + 1) > 0 := by
    have h3 : Real.sqrt (y^2 + 1) > 0 := by
      apply Real.sqrt_pos.2
      nlinarith
    have h4 : Real.sqrt (y^2 + 1) > abs y := by
      cases' abs_cases y with h5 h5
      · -- y ≥ 0
        nlinarith [Real.sqrt_nonneg (y^2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ y^2 + 1 by nlinarith)]
      · -- y < 0
        nlinarith [Real.sqrt_nonneg (y^2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ y^2 + 1 by nlinarith)]
    cases' abs_cases y with h5 h5
    · -- y ≥ 0
      linarith
    · -- y < 0
      linarith
  
  have hsq1 : Real.sqrt (x^2 + 1) ^2 = x^2 + 1 := by 
    rw [Real.sq_sqrt]
    nlinarith

  have hsq2 : Real.sqrt (y^2 + 1) ^2 = y^2 + 1 := by 
    rw [Real.sq_sqrt]
    nlinarith
  
  have h3 : x + y = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (Real.sqrt (x^2 + 1) - Real.sqrt (y^2 + 1)), 
        sq_nonneg (x + y), 
        Real.sqrt_nonneg (x^2 + 1), Real.sqrt_nonneg (y^2 + 1), 
        mul_pos (show (0 : ℝ) < x + Real.sqrt (x^2 + 1) by linarith) (show (0 : ℝ) < y + Real.sqrt (y^2 + 1) by linarith)
      ]
  
  exact h3