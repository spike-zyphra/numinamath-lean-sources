import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

theorem inequalities_146891
  (a b c : ℝ)
  (h₀ : 0 < a)
  (h₁ : 0 < b)
  (h₂ : 0 < c)
  (h₃ : c < a + b)
  (h₄ : b < a + c)
  (h₅ : a < b + c) :
  a / (b + c) + b / (c + a) + c / (a + b) ≤ 2 := by 
  have pos1 : 0 < b + c := by linarith
  have pos2 : 0 < c + a := by linarith
  have pos3 : 0 < a + b := by linarith
  have h6 : a / (b + c) + b / (c + a) + c / (a + b) - 2 ≤ 0 := by 
    have pos4 : 0 < (b + c) * (c + a) * (a + b) := by
      positivity
    have h7 : a / (b + c) + b / (c + a) + c / (a + b) - 2 = 
        (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 2 * (b + c) * (c + a) * (a + b)) / ( (b + c) * (c + a) * (a + b) ) := by 
      field_simp
      <;> 
      ring 
    rw [h7] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is non-positive
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_pos_of_pos h₀, sq_pos_of_pos h₁, sq_pos_of_pos h₂,
        mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂,
        mul_pos (show 0 < a + b - c by linarith) (show 0 < a + c - b by linarith),
        mul_pos (show 0 < a + b - c by linarith) (show 0 < b + c - a by linarith),
        mul_pos (show 0 < a + c - b by linarith) (show 0 < b + c - a by linarith)
      ]
    · -- Show that the denominator is non-negative
      positivity
  linarith