import Mathlib

theorem algebra_18825 (p q a b: ℝ) (h₀ : a * 2 + b = -5) (h₁ : a * p + b = -14) (h₂ : a * (p + 2) + b = -17)
    (h₃ : a * 13 + b = q) :
    p + q = -13.5 := by
  have ha : a = -3 / 2 := by
    linarith [h₁, h₂]
  have hb : b = -2 := by
    rw [ha] at h₀
    linarith
  have hp : p = 8 := by
    rw [ha, hb] at h₁
    linarith
  have hq : q = -43 / 2 := by
    rw [ha, hb] at h₃
    linarith
  rw [hp, hq]
  norm_num