import Mathlib

theorem inequalities_120672 (a b : ℝ) :
    Real.sqrt ((a^2 + b^2) / 2) ≥ (a + b) / 2 := by
  have h1 : ((a + b) / 2) ^ 2 ≤ ((a ^ 2 + b ^ 2) / 2) := by
    nlinarith [sq_nonneg (a - b)]
  by_cases h : (a + b) / 2 ≥ 0
  · -- If $(a + b)/2 \geq 0$, we can apply the squaring approach
    have h2 : (Real.sqrt ((a ^ 2 + b ^ 2) / 2)) ^ 2 = (a ^ 2 + b ^ 2) / 2 := Real.sq_sqrt (by 
      positivity 
    )
    nlinarith [Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2), Real.sq_sqrt (show ((a ^ 2 + b ^ 2) / 2) ≥ 0 by positivity), h1]
  · -- Case where $(a + b)/2 < 0$
    have h' : (a + b) / 2 < 0 := by linarith
    have h3 : Real.sqrt ((a ^ 2 + b ^ 2) / 2) ≥ 0 := Real.sqrt_nonneg ((a ^ 2 + b ^ 2) / 2)
    nlinarith [h3, show (a + b) / 2 < 0 by linarith, show Real.sqrt ((a ^ 2 + b ^ 2) / 2) ≥ 0 by apply Real.sqrt_nonneg]