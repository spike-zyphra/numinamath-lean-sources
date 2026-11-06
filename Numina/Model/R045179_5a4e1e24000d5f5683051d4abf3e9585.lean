import Mathlib

theorem inequalities_30443 (A a B b C c r : ℝ) (h₀ : 0 < A) (h₁ : 0 < a) (h₂ : 0 < B)
    (h₃ : 0 < b) (h₄ : 0 < C) (h₅ : 0 < c) (h₆ : 0 < r) :
    (A + a + B + b) / (A + a + B + b + c + r) +
    (B + b + C + c) / (B + b + C + c + a + r) >
    (C + c + A + a) / (C + c + A + a + b + r) := by
  have hx1 : 0 < (A + a + B + b + c + r) := by linarith
  have hx2 : 0 < (B + b + C + c + a + r) := by linarith
  have hx3 : 0 < (C + c + A + a + b + r) := by linarith
  have h7 : ( (A + a + B + b) / (A + a + B + b + c + r) + (B + b + C + c) / (B + b + C + c + a + r) ) - ( (C + c + A + a) / (C + c + A + a + b + r) ) > 0 := by
    have h8 : ( (A + a + B + b) / (A + a + B + b + c + r) + (B + b + C + c) / (B + b + C + c + a + r) ) - ( (C + c + A + a) / (C + c + A + a + b + r) ) =
      ( (A + a + B + b) * (B + b + C + c + a + r) * (C + c + A + a + b + r) +
      (B + b + C + c) * (A + a + B + b + c + r) * (C + c + A + a + b + r) - (C + c + A + a) * (A + a + B + b + c + r) * (B + b + C + c + a + r) ) / ( (A + a + B + b + c + r) * (B + b + C + c + a + r) * (C + c + A + a + b + r) ) := by 
      field_simp
      <;> ring
    rw [h8] at *
    apply div_pos
    · -- Show that the numerator is positive.
      nlinarith [sq_nonneg (A - C), sq_nonneg (a - c), sq_nonneg (B - A), sq_nonneg (b - a), sq_nonneg (C - B), sq_nonneg (c - b), 
        sq_nonneg (A + a - (B + b)), sq_nonneg (B + b - (C + c)), sq_nonneg (C + c - (A + a)), 
          mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₀ h₃, mul_pos h₀ h₄, mul_pos h₀ h₅, mul_pos h₀ h₆, 
          mul_pos h₁ h₂, mul_pos h₁ h₃, mul_pos h₁ h₄, mul_pos h₁ h₅, mul_pos h₁ h₆, 
          mul_pos h₂ h₃, mul_pos h₂ h₄, mul_pos h₂ h₅, mul_pos h₂ h₆, 
          mul_pos h₃ h₄, mul_pos h₃ h₅, mul_pos h₃ h₆, 
          mul_pos h₄ h₅, mul_pos h₄ h₆, mul_pos h₅ h₆
      ]
    · -- Show that the denominator is positive.
      positivity
  linarith [h7]