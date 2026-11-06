import Mathlib

/-if a + b - 2√(a-1) - 4√(b-2) = 3√(c-3) - c/2 - 5, then, the value of a+b+c is 20-/
theorem algebra_314637 {a b c : ℝ} (ha : 1 ≤ a) (hb : 2 ≤ b) (hc : 3 ≤ c)
    (h : a + b - 2 * Real.sqrt (a - 1) - 4 * Real.sqrt (b - 2) =
      3 * Real.sqrt (c - 3) - (1 / 2) * c - 5) :
    a + b + c = 20 := by
    -- we first prove some fundamental inequalities --
  have h1 : Real.sqrt (a - 1) ≥ 0 := Real.sqrt_nonneg (a - 1)
  have h2 : Real.sqrt (b - 2) ≥ 0 := Real.sqrt_nonneg (b - 2)
  have h3 : Real.sqrt (c - 3) ≥ 0 := Real.sqrt_nonneg (c - 3)
  
-- simplifying the equation, giving the key identity --
  have h4 : (Real.sqrt (a - 1) - 1) ^ 2 + (Real.sqrt (b - 2) - 2) ^ 2 + (Real.sqrt (c - 3) - 3) ^ 2 = 0 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ a - 1 by linarith), Real.sq_sqrt (show 0 ≤ b - 2 by linarith),
      Real.sq_sqrt (show 0 ≤ c - 3 by linarith),
      sq_nonneg (Real.sqrt (a - 1) - 1), sq_nonneg (Real.sqrt (b - 2) - 2),
      sq_nonneg (Real.sqrt (c - 3) - 3)]
  
  -- from the identity, we see that all the terms are zero --
  have h5 : Real.sqrt (a - 1) = 1 := by nlinarith [sq_nonneg (Real.sqrt (a - 1) - 1), sq_nonneg (Real.sqrt (b - 2) - 2), sq_nonneg (Real.sqrt (c - 3) - 3)]
  
  have ha_eq : a = 2 := by
    have hsqrt : Real.sqrt (a - 1) = 1 := by linarith
    have h1 : (Real.sqrt (a - 1)) ^ 2 = (1 : ℝ) ^ 2 := by
      rw [hsqrt]
    have h2 : (Real.sqrt (a - 1)) ^ 2 = a - 1 := Real.sq_sqrt (by linarith)
    have h3 : (1 : ℝ) ^ 2 = 1 := by norm_num
    nlinarith
  
  have h6 : Real.sqrt (b - 2) = 2 := by nlinarith [sq_nonneg (Real.sqrt (a - 1) - 1), sq_nonneg (Real.sqrt (b - 2) - 2), sq_nonneg (Real.sqrt (c - 3) - 3)]
  
  have hb_eq : b = 6 := by
    have hsqrt : Real.sqrt (b - 2) = 2 := by linarith
    have h1 : (Real.sqrt (b - 2)) ^ 2 = (2 : ℝ) ^ 2 := by
      rw [hsqrt]
    have h2 : (Real.sqrt (b - 2)) ^ 2 = b - 2 := Real.sq_sqrt (by linarith)
    have h3 : (2 : ℝ) ^ 2 = 4 := by norm_num
    nlinarith
  
  have h7 : Real.sqrt (c - 3) = 3 := by nlinarith [sq_nonneg (Real.sqrt (a - 1) - 1), sq_nonneg (Real.sqrt (b - 2) - 2), sq_nonneg (Real.sqrt (c - 3) - 3)]
  
  have hc_eq : c = 12 := by
    have hsqrt : Real.sqrt (c - 3) = 3 := by linarith
    have h1 : (Real.sqrt (c - 3)) ^ 2 = (3 : ℝ) ^ 2 := by
      rw [hsqrt]
    have h2 : (Real.sqrt (c - 3)) ^ 2 = c - 3 := Real.sq_sqrt (by linarith)
    have h3 : (3 : ℝ) ^ 2 = 9 := by norm_num
    nlinarith
-- finally, plug them into the expression a + b + c --
  linarith [ha_eq, hb_eq, hc_eq]