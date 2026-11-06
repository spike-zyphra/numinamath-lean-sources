import Mathlib

theorem inequalities_316934
    (a b c : ℝ)
    (h₀ : 0 < a)
    (h₁ : 0 < b)
    (h₂ : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  have h1 : b + c > 0 := by nlinarith
  have h2 : c + a > 0 := by nlinarith
  have h3 : a + b > 0 := by nlinarith
  have h4 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h5 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
        (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 3 / 2 * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by 
      field_simp
      <;> ring 
    rw [h5]
    apply div_nonneg 
    nlinarith [mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂, 
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
      mul_pos (show 0 < a + b by linarith) (show 0 < a + c by linarith), 
      mul_pos (show 0 < a + b by linarith) (show 0 < b + c by linarith), 
      mul_pos (show 0 < a + c by linarith) (show 0 < b + c by linarith)]
    positivity
  linarith