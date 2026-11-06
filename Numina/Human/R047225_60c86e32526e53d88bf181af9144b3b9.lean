import Mathlib

theorem algebra_15204 {x y : ℝ} (h₀ : |x - y| = 9) (h₁ : x^2 + y^2 = 153) :
    x * y = 36 := by
  have h2 : (x - y) ^ 2 = 81 := by
    calc
      (x - y) ^ 2 = |x - y| ^ 2 := by rw [sq_abs]
      _ = 9 ^ 2 := by rw [h₀]
      _ = 81 := by norm_num
  linarith