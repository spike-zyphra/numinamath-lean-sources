import Mathlib

open Real

theorem inequalities_316999 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a^2 + b^2 = c^2) :
    (a^3 + b^3 + c^3) / (a * b * c) ≥ 2 + sqrt 2 := by
  have h1 : 0 < a * b * c := by
    positivity
  have h3 : a^3 + b^3 + c^3 ≥ (2 + sqrt 2) * (a * b * c) := by
    have h24 : c = Real.sqrt (a^2 + b^2) := by
      have hc2 : c > 0 := by linarith
      have hc3 : c^2 = a^2 + b^2 := by linarith
      have : c = Real.sqrt (a^2 + b^2) := by
        rw [← hc3]
        field_simp [hc2]
        <;> linarith
        all_goals linarith
      linarith
    rw [show c = Real.sqrt (a^2 + b^2) by linarith [h24]]
    have h14 : a^3 + b^3 + (Real.sqrt (a^2 + b^2))^3 - (2 + sqrt 2) * (a * b * Real.sqrt (a^2 + b^2)) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a^2 + b^2 - 2 * a * b), sq_nonneg (Real.sqrt (a^2 + b^2) - a * Real.sqrt 2), sq_nonneg (Real.sqrt (a^2 + b^2) - b * Real.sqrt 2), 
              Real.sqrt_nonneg (a^2 + b^2), 
              sq_nonneg (Real.sqrt (a^2 + b^2) ^ 2 - 2 * a^2), 
              sq_nonneg (Real.sqrt (a^2 + b^2) ^ 2 - 2 * b^2), 
              Real.sq_sqrt (show a ^ 2 + b ^ 2 ≥ 0 by positivity), 
              Real.sqrt_nonneg (2 : ℝ), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
              Real.sqrt_nonneg (2 : ℝ), 
              mul_pos ha hb, 
              sq_nonneg (a - b), 
              mul_pos ha (show 0 < a * b by positivity), 
              mul_pos (show 0 < a * b by positivity) hb, 
              sq_nonneg (a * b), 
              sq_nonneg (Real.sqrt (a^2 + b^2) - a), 
              sq_nonneg (Real.sqrt (a^2 + b^2) - b)]
    linarith
    all_goals nlinarith
    all_goals nlinarith
    all_goals linarith
  have h4 : (a^3 + b^3 + c^3) / (a * b * c) ≥ 2 + Real.sqrt 2 := by
    have h5 : a * b * c > 0 := by positivity
    apply (le_div_iff₀ h5).mpr
    linarith [h3]
  linarith [h4]
  all_goals nlinarith
  all_goals nlinarith
  all_goals linarith
  all_goals linarith