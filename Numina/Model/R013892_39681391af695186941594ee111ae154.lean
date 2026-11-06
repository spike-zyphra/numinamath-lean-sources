import Mathlib

theorem algebra_148819 (x : ℝ) (hx : 1 ≤ x ∧ x ≤ 9) :
    |(6 * x + 6) / (x + 11) - Real.sqrt x| < 0.05 := by
  have h1 : 1 ≤ x := hx.1
  have h2 : x ≤ 9 := hx.2
  have h3 : 0 < x + 11 := by 
    linarith
  have h3' : 0 < x + 11 := h3
  -- First, we show the upper bound
  have h4 : (6 * x + 6) / (x + 11) - Real.sqrt x < (0.05 : ℝ) := by
    have h8 : (6 * x + 6) / (x + 11) < Real.sqrt x + (0.05 : ℝ) := by 
      have hx1 : 0 < (x + 11) := h3
      have hx2 : 0 < (Real.sqrt x + (0.05 : ℝ)) := by
        have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
        linarith [hsqrt0]
      have h9 : (6 * x + 6) < (Real.sqrt x + (0.05 : ℝ)) * (x + 11) := by 
        nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith), 
            sq_nonneg ((6 * x + 6) - (Real.sqrt x + (0.05 : ℝ)) * (x + 11)), 
            sq_nonneg (Real.sqrt x - 3), sq_nonneg (x - 1), sq_nonneg (x - 9), 
            mul_nonneg (show 0 ≤ x - 1 by linarith) (show 0 ≤ 9 - x by linarith), 
            Real.sqrt_le_sqrt (show (0 : ℝ) ≤ x by linarith)
          ]
      have hx7 : (6 * x + 6) / (x + 11) < Real.sqrt x + (0.05 : ℝ) := by 
        apply (div_lt_iff₀ (by linarith)).mpr 
        linarith 
      linarith 
    linarith
  -- Now, we show the lower bound
  have h5 : - (0.05 : ℝ) < (6 * x + 6) / (x + 11) - Real.sqrt x := by 
    have h6a : Real.sqrt x - (0.05 : ℝ) < (6 * x + 6) / (x + 11) := by 
      have h6a1 : Real.sqrt x - (0.05 : ℝ) > 0 := by 
        have hsqrt1 : Real.sqrt x ≥ (1 : ℝ) := by 
          have h11 : 1 ≤ x := h1 
          have h12 : Real.sqrt x ≥ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ x by linarith)
          have h13 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one 
          linarith [h12, h13] 
        nlinarith
      have h8 : (Real.sqrt x - (0.05 : ℝ)) < (6 * x + 6) / (x + 11) := by 
        have hx1 : 0 < (x + 11) := h3 
        apply (lt_div_iff₀ (by linarith)).mpr 
        have h11 : (Real.sqrt x - (0.05 : ℝ)) * (x + 11) < (6 * x + 6) := by 
          have hx5 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (show 0 ≤ x by linarith)
          nlinarith [Real.sqrt_nonneg x, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg x), 
              sq_nonneg (Real.sqrt x ^ 2 - x), sq_nonneg (Real.sqrt x - 3), sq_nonneg (x - 1), sq_nonneg (x - 9), 
              Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - 1), 
              h1, h2, 
              mul_nonneg (show (0 : ℝ) ≤ x - 1 by linarith) (show (0 : ℝ) ≤ 9 - x by linarith)
            ]
        linarith
      linarith
    linarith [h6a]
  -- Now, we can apply the absolute value inequality property
  apply abs_lt.mpr
  constructor <;> linarith [h4, h5]