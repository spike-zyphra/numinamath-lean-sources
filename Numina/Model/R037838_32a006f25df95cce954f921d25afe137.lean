import Mathlib

theorem algebra_322920 (a b c : ℝ) (h₀ : a ≠ 0) (h₁ : a * 1 + b * 1 + c = 0)
    (h₂ : a * 5 + b * 5 + c = 0) (h₃ : ∀ x, a * x + b * x + c ≤ 2 * x) :
    (a * (-b / (2 * a)) + b * (-b / (2 * a)) + c) * (a * (-b / (2 * a)) ^ 2 +
    b * (-b / (2 * a)) + c) = 4 := by
  have h4 : b = -a := by
    linarith
  have h5 : c = 0 := by
    rw [show b = -a by linarith] at h₁
    linarith
  have h7 : a * (-1 : ℝ) + b * (-1 : ℝ) + c ≤ 2 * (-1 : ℝ) := by
    apply h₃
  rw [show b = -a by linarith, show c = (0 : ℝ) by linarith] at h7
  norm_num at h7 
  all_goals nlinarith