import Mathlib

theorem algebra_102961 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 2013) :
    Real.sqrt (3 * a + 12) + Real.sqrt (3 * b + 12) + Real.sqrt (3 * c + 12) ≤ 135 := by
  have h2 : (Real.sqrt (3 * a + 12) + Real.sqrt (3 * b + 12) + Real.sqrt (3 * c + 12)) ^ 2 ≤ 3 * ((3 * a + 12) + (3 * b + 12) + (3 * c + 12)) := by
    nlinarith [sq_nonneg (Real.sqrt (3 * a + 12) - Real.sqrt (3 * b + 12)), 
          sq_nonneg (Real.sqrt (3 * a + 12) - Real.sqrt (3 * c + 12)), 
          sq_nonneg (Real.sqrt (3 * b + 12) - Real.sqrt (3 * c + 12)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 * a + 12 by nlinarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 * b + 12 by nlinarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 * c + 12 by nlinarith), 
          Real.sqrt_nonneg (3 * a + 12), Real.sqrt_nonneg (3 * b + 12), Real.sqrt_nonneg (3 * c + 12)]
  have h3 : (3 * a + 12 + 3 * b + 12 + 3 * c + 12) = 3*(2013) + 36 := by 
    nlinarith [h]
  have h8 : (3 * a + 12 + 3 * b + 12 + 3 * c + 12) = (6075 : ℝ):= by 
    nlinarith [h3]
  -- Derive the final from h and h2 and h3
  have h6 : (Real.sqrt (3 * a + 12) + Real.sqrt (3 * b + 12) + Real.sqrt (3 * c + 12)) ^ 2 ≤ (18225 : ℝ):= by 
    nlinarith [h2, h8]
  -- Prove that $\sqrt{18225} = 135$.
  have h7 : Real.sqrt ((18225) : ℝ) = (135 : ℝ):= by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  -- Prove: $\sqrt{X^2} = X$, for non-negative variables.
  have h9 : Real.sqrt (3 * a + 12) + Real.sqrt (3 * b + 12) + Real.sqrt (3 * c + 12) = Real.sqrt ((Real.sqrt (3 * a + 12) + Real.sqrt (3 * b + 12) + Real.sqrt (3 * c + 12)) ^ 2 ) := by 
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg]
    positivity 
  -- Prove that $Y \leq Z$ inequality, using the above.
  nlinarith [h9, h7, h6]