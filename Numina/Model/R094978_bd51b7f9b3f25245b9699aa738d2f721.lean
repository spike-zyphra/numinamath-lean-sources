import Mathlib

theorem algebra_264168 {a b c : ℝ} (h₀ : a + b = 3) (h₁ : a * c + b = 18)
    (h₂ : b * c + a = 6) : c = 7 := by
  have ha : a = 3 - b := by linarith
  rw [ha] at h₁
  rw [ha] at h₂
  have eq1 : 3 * c + b - b * c = 18 := by 
    nlinarith
  have eq2 : b * (c - 1) = 3 := by
    nlinarith
  have eq3 : b * c = b + 3 := by
    linarith
  have h4 : 3 * c - 3 = 18 := by
    nlinarith [eq1, eq3]
  linarith