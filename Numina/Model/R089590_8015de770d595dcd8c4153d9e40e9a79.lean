import Mathlib

theorem algebra_306819 {a b : ℝ} (h₀ : a < b) (h₁ : b < 0) (h₂ : a^2 + b^2 = 4 * a * b) :
    (a + b) / (a - b) = Real.sqrt 3 := by
  have h3 : a < 0 := by linarith
  have h4 : a - b < 0 := by linarith
  have h5 : a + b < 0 := by nlinarith
  have h6 : (a + b) ^ 2 = 6 * (a * b) := by
    nlinarith
  have h7 : (a - b) ^ 2 = 2 * (a * b) := by
    nlinarith
  have h8 : (a + b) / (a - b) = Real.sqrt 3 := by
    have h9 : ((a + b) / (a - b)) ^ 2 = 3 := by
      have h10 : a - b ≠ 0 := by linarith
      have h11 : (a + b) ^ 2 = 6 * (a * b) := h6
      have h12 : (a - b) ^ 2 = 2 * (a * b) := h7
      calc
        ((a + b) / (a - b)) ^ 2
            = ( (a + b) ^ 2 ) / ( (a - b) ^ 2 ) := by field_simp [h10] -- transform ((a + b)/(a - b))^2 to ((a + b)^2)/((a - b)^2)
        _ = (6 * (a * b)) / (2 * (a * b)) := by
          rw [h11, h12]
          -- Simplify ((a + b)^2)/((a - b)^2)
        _ = 3 := by
          have h15 : a * b ≠ 0 := by nlinarith  -- since a < 0 and b < 0, a*b > 0
          field_simp [h15]
          <;> nlinarith
    have h14 : (a + b) / (a - b) > 0 := by
      apply div_pos_of_neg_of_neg
      all_goals nlinarith
      all_goals nlinarith
    have h10 : (a + b) / (a - b) = Real.sqrt 3 := by
      have h15 : Real.sqrt 3 = Real.sqrt ( ( (a + b) / (a - b) ) ^ 2 ) := by
        rw [h9]
      have h16 : ( (a + b) / (a - b) ) = Real.sqrt ( ( (a + b) / (a - b) ) ^ 2 ) := by
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_pos h14]
      linarith [h15, h16]
      all_goals nlinarith
      all_goals nlinarith
    exact h10
  exact h8