import Mathlib

theorem algebra_185085 (x : ℝ) (hx : x = (Real.sqrt 5 - 3) / 2) :
    x * (x + 1) * (x + 2) * (x + 3) / ((x - 1) * (x + 4)) = 1 / 5 := by
  have h1 : x ^ 2 + 3 * x + 1 = 0 := by
    rw [hx]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h2 : x * (x + 1) * (x + 2) * (x + 3) = -1 := by
    calc
      x * (x + 1) * (x + 2) * (x + 3) = (x ^ 2 + 3 * x) * (x ^ 2 + 3 * x + 2) := by ring
      _ = (-1) * ((-1) + 2) := by
        have eq1 : x ^ 2 + 3 * x = -1 := by linarith [h1]
        rw [eq1]
      _ = (-1) * (1) := by ring
      _ = -1 := by ring
  have h3 : (x - 1) * (x + 4) = -5 := by
    calc
      (x - 1) * (x + 4) = x^2 + 3 * x - 4 := by ring
      _ = (-1) - 4 := by
        nlinarith [h1]
      _ = -5 := by ring
  have h4 : x * (x + 1) * (x + 2) * (x + 3) / ((x - 1) * (x + 4)) = 1 / 5 := by
    rw [show x * (x + 1) * (x + 2) * (x + 3) = -1 by linarith [h2], show (x - 1) * (x + 4) = -5 by linarith [h3]]
    all_goals norm_num
  exact h4