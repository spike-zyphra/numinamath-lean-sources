import Mathlib

theorem algebra_3496 {a b : ℝ} (h₀ : a + b = -6 / 5) (h₁ : 2 * a - 3 * b = 5 / 3) :
   4 * a ^ 2 - 2 * a * b - 6 * b ^ 2 + 2018 = 2014 := by
  have hb : b = -6 / 5 - a := by linarith
  rw [hb] at h₁
  have ha : a = -29 / 75 := by
    linarith
  have hb2 : b = -61 / 75 := by
    rw [ha] at hb
    linarith
  rw [ha, hb2]
  norm_num