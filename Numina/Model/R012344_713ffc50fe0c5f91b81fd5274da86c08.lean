import Mathlib.Tactic

theorem inequalities_129362 (x : ℝ) (hx : 1 ≤ x) :
    Real.sqrt x - Real.sqrt (x - 1) > Real.sqrt (x + 1) - Real.sqrt x := by
  have h1 : 0 ≤ x - 1 := by linarith
  have h2 : 0 ≤ x := by linarith
  have h3 : 0 ≤ x + 1 := by linarith
  have h4 : Real.sqrt x ≥ 0 := by positivity
  have h5 : Real.sqrt (x - 1) ≥ 0 := by positivity
  have h6 : Real.sqrt (x + 1) ≥ 0 := by positivity

  have h7 : Real.sqrt x - Real.sqrt (x - 1) > Real.sqrt (x + 1) - Real.sqrt x := by
    have h11 : Real.sqrt x - Real.sqrt (x - 1) - (Real.sqrt (x + 1) - Real.sqrt x) > 0 := by
      have h8 : Real.sqrt x ≥ 0 := by positivity
      have h9 : Real.sqrt (x - 1) ≥ 0 := by positivity
      have h10 : Real.sqrt (x + 1) ≥ 0 := by positivity

      have h15 : 2 * Real.sqrt x > Real.sqrt (x - 1) + Real.sqrt (x + 1) := by
        have h16 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)
        have h17 : Real.sqrt (x - 1) ^ 2 = x - 1 := Real.sq_sqrt (show (0 : ℝ) ≤ x - 1 by linarith)
        have h18 : Real.sqrt (x + 1) ^ 2 = x + 1 := Real.sq_sqrt (show (0 : ℝ) ≤ x + 1 by linarith)
        have h19 : (Real.sqrt (x - 1) + Real.sqrt (x + 1)) ^ 2 < (2 * Real.sqrt x) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg x,
            h16, h17, h18, 
            mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (x - 1)), 
            mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (x + 1)), 
            mul_nonneg (Real.sqrt_nonneg (x - 1)) (Real.sqrt_nonneg (x + 1)), 
            sq_nonneg (Real.sqrt x ^ 2 - (Real.sqrt (x - 1) ^ 2 + Real.sqrt (x + 1) ^ 2)/2), 
            sq_nonneg (Real.sqrt (x) - Real.sqrt (x-1)), sq_nonneg (Real.sqrt (x) - Real.sqrt (x+1)), 
            sq_nonneg (Real.sqrt (x-1) - Real.sqrt (x+1)), Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x + 1)]
        nlinarith [Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x + 1), sq_nonneg (Real.sqrt x - (Real.sqrt (x - 1) + Real.sqrt (x + 1)) / 2), 
          sq_nonneg (Real.sqrt (x) - Real.sqrt (x - 1)), sq_nonneg (Real.sqrt (x) - Real.sqrt (x + 1)), sq_nonneg (Real.sqrt (x - 1) - Real.sqrt (x + 1)), Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (x + 1)]
      linarith
    linarith
  exact h7