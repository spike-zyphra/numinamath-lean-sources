import Mathlib

theorem algebra_1705 {a b c : ℝ} (h₀ : a > b) (h₁ : b > c) :
    (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) > (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) := by 
  have h2 : a - b > 0 := by linarith
  have h3 : b - c > 0 := by linarith
  have h4 : a - c > 0 := by linarith
  have h : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) - (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) = (a - b) * (a - c) * (b - c) := by 
    ring
  have h' : (a - b) * (a - c) * (b - c) > 0 := by 
    apply mul_pos
    apply mul_pos
    all_goals linarith
  linarith [h, h']