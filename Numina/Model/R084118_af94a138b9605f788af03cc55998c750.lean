import Mathlib

theorem inequalities_278592 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b)^2 / 2 + (a + b) / 4 ≥ a * Real.sqrt b + b * Real.sqrt a := by
  have h1 : 0 ≤ Real.sqrt a := by positivity
  have h2 : 0 ≤ Real.sqrt b := by positivity
  have h3 : Real.sqrt a ^ 2 = a := Real.sq_sqrt (by linarith [ha])
  have h4 : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by linarith [hb])
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), sq_nonneg (Real.sqrt a - 1 / 2), sq_nonneg (Real.sqrt b - 1 / 2), 
            mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), 
            h3, h4, Real.sqrt_nonneg a, Real.sqrt_nonneg b, 
            sq_nonneg (Real.sqrt a ^ 2 - Real.sqrt b ^ 2), sq_nonneg (Real.sqrt a + Real.sqrt b), 
            mul_nonneg (show 0 ≤ (Real.sqrt a : ℝ) by positivity) (show 0 ≤ (Real.sqrt b : ℝ) by positivity)
          ]