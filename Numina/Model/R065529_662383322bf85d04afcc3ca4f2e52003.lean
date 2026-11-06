import Mathlib

theorem algebra_144463 {a b : ℝ} (h₀ : a - b = 3) (h₁ : 2 * (a - b) / 3 - (a + 2 * b) / 9 = 1) :
    (a^2 - a * b + b^2) / (2 * a^2 - 6 * b) = 1 / 2 := by
  have ha : a = b + 3 := by linarith
  have hb : b = 2 := by
    rw [ha] at h₁
    linarith
  have ha2 : a = 5 := by
    linarith [hb]
  rw [ha2, hb]
  norm_num