import Mathlib

open Real

theorem inequalities_599468 (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) (hx : 1 < x)
    (h : sqrt a + 1 > sqrt b) : a * x + x / (x - 1) > b := by

  have h1 : 0 < x - 1 := by linarith
  have h2 : (sqrt a + 1) ^ 2 > b := by
    have h3 : sqrt a + 1 > sqrt b := h
    have h4 : (sqrt a + 1) ^ 2 > (sqrt b) ^ 2 := by nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, h3]
    have h5 : (sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith)
    nlinarith

  have h3 : a * x + x / (x - 1) - b > 0 := by
    have h5 : 0 < x - 1 := h1
    have h6 : a * x + x / (x - 1) - b > 0 := by
      have h7 : a * x + x / (x - 1) - b = (a * (x) * (x - 1) + x - b * (x - 1) ) / (x - 1) := by
        field_simp
        <;> ring
      rw [h7]
      apply div_pos
      · -- Show the numerator is positive
        have h8 : 0 < a * (x) * (x - 1) + x - b * (x - 1) := by
          nlinarith [sq_nonneg (x - (1 + 1 / sqrt a)), sq_nonneg (sqrt a * (x -1 ) - 1), 
            sq_nonneg (x -1 ), sq_nonneg (sqrt a -1 ), 
            Real.sqrt_pos.mpr (show (0 : ℝ) < a by linarith), 
            Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), 
            Real.sqrt_nonneg a, Real.sqrt_nonneg (a), 
            h2, Real.sqrt_nonneg a, sq_nonneg (x -1 ), sq_nonneg (a -1 ), 
            sq_nonneg (sqrt a * (x -2 )), 
            mul_pos ha (show 0 < x -1 by nlinarith)
          ]
        linarith
      · -- Show the denominator is positive
        all_goals linarith
    linarith
  linarith