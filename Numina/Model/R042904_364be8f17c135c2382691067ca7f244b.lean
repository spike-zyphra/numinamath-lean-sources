import Mathlib
theorem algebra_106814 (x y z t : ℝ) (h₁ : x^2 + y^2 = 4) (h₂ : z^2 + t^2 = 9) (h₃ : x*t + y*z ≥ 6) : x + z ≤ Real.sqrt 13 := by
  have h4 : (x + z) ^ 2 ≤ 13 := by
    nlinarith [sq_nonneg (x - z), sq_nonneg (y - t), 
          sq_nonneg (x * t - y * z), 
          sq_nonneg (y - t), 
          mul_self_nonneg (x - z), 
          mul_self_nonneg (y - t),
          sq_nonneg (y * z - x * t)
    ]
  have h5 : (x + z) ^ 2 ≤ 13 := h4
  have h6 : (x + z) ≤ Real.sqrt 13 := by
    have h7 : (x + z) ^ 2 ≤ (13 : ℝ) := h4
    have h8 : 0 ≤ (13 : ℝ) := by norm_num
    have h9 : (x + z) ≤ Real.sqrt 13 := by
      apply Real.le_sqrt_of_sq_le 
      linarith
    exact h9
  exact h6