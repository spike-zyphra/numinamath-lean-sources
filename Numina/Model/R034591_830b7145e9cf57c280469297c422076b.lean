import Mathlib

open Real

theorem inequalities_309665 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a^2 + b^2 = c^2) :
    (a^3 + b^3 + c^3) / (a * b * c) ≥ 2 + sqrt 2 := by

  have pos1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc

  have h1 : a^3 + b^3 + c^3 ≥ (2 + Real.sqrt 2) * (a * b * c) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a * b), sq_nonneg (c - a * Real.sqrt 2), sq_nonneg (c - b * Real.sqrt 2), 
          sq_nonneg (a^2 + b^2 - c^2), 
          sq_nonneg (a * b - b * (c * Real.sqrt 2 / 2)), sq_nonneg (a * b - a * (c * Real.sqrt 2 / 2)), 
          Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          mul_pos ha hb, 
          mul_pos ha hc, 
          mul_pos hb hc, 
          h, 
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2)
        ]

  have h2 : (a^3 + b^3 + c^3) / (a * b * c) ≥ (2 + Real.sqrt 2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  exact h2