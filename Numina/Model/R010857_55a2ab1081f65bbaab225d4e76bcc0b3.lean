import Mathlib

theorem algebra_93536 (P H L : ℝ) (hp : 0 < P) (hh : 0 < H) (hl: 0 < L)
(h₁ : (P + H)*(8 - L) = 50 / 100) (h₂ : (6 + (12:ℝ)/60 - L) * H = 24 / 100) (h₃ : (11 + (12:ℝ)/60 - L) * P = 26 / 100) : L * 60 = 48 := by 
  nlinarith [mul_pos hp hh, mul_pos hp hl, mul_pos hh hl]