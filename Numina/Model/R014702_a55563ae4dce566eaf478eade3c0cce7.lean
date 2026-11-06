import Mathlib

theorem inequalities_603117
    (a b c : ℝ)
    (h₀ : 0 < a)
    (h₁ : 0 < b)
    (h₂ : 0 < c)
    (h₃ : a * b * c = 1) :
    1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) ≤ 1 := by 
  have h4 : 0 < (1 + a + b) * (1 + b + c) * (1 + c + a) := by
    positivity
  have h5 : 1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) - 1 ≤ 0 := by
    have h6 : 1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + c + a) - 1 = 
      ( (1 + c + a) * (1 + b + c) + (1 + a + b) * (1 + c + a) + (1 + a + b) * (1 + b + c) - (1 + a + b) * (1 + b + c) * (1 + c + a) ) / ( (1 + a + b) * (1 + b + c) * (1 + c + a) ) := by 
      field_simp 
      <;> ring 
    rw [h6] at *
    apply div_nonpos_of_nonpos_of_nonneg 
    · 
      nlinarith [ sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), 
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          sq_nonneg (a * b * c - 1), h₃, 
          mul_pos h₀ h₁, mul_pos h₁ h₂, mul_pos h₀ h₂ 
          ]
    · 
      positivity 
  linarith