import Mathlib

open Real

theorem inequalities_8752
    (a b c : ℝ)
    (h₀ : 0 < a)
    (h₁ : 0 < b)
    (h₂ : 0 < c)
    (h₃ : a * b * c = 1) :
    1 / 3 ≤ a / ((a + 2) * (b + 2)) + b / ((b + 2) * (c + 2)) + c / ((c + 2) * (a + 2)) := by 
  have ha1 : 0 < a + 2 := by linarith
  have hb1 : 0 < b + 2 := by linarith
  have hc1 : 0 < c + 2 := by linarith
  
  have h4 : a / ((a + 2) * (b + 2)) + b / ((b + 2) * (c + 2)) + c / ((c + 2) * (a + 2)) - 1 / 3 ≥ 0 := by
    have pos1 : 0 < (a + 2) * (b + 2) * (c + 2) := by positivity
    have h5 : (a / ((a + 2) * (b + 2)) + b / ((b + 2) * (c + 2)) + c / ((c + 2) * (a + 2)) - 1 / 3) =
               ( (a * (c + 2) + b * (a + 2) + c * (b + 2) - (1 / 3) * ( (a + 2) * (b + 2) * (c + 2) )) / ((a + 2) * (b + 2) * (c + 2)) ) := by 
      field_simp
      ring
    rw [h5]
    apply div_nonneg
    -- Prove numerator is non-negative
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      h₀, h₁, h₂, h₃, mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂]
    all_goals positivity
  
  linarith