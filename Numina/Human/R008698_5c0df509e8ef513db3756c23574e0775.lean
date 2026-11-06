import Mathlib
open Real

/- Given an odd function $f(x)$ defined on the set of real numbers $\mathbb{R}$, where for $x > 0$, $f(x) = \frac{3^x - 4}{3^x}$, find the value of $f[f(\log_{3}2)]$. -/
theorem algebra_9140 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hfpos : ∀ x > 0, f x = (3 ^ x - 4) / 3 ^ x) :
    f (f (logb 3 2)) = 1 / 3 := by
  --   f (f (logb 3 2))
  -- = f ((3 ^ logb 3 2 - 4) / 3 ^ logb 3 2)
  -- = f ((2 - 4) / 2)
  -- = f (-1)
  -- = -f 1
  -- = -((3 ^ 1 - 4) / 3 ^ 1)
  -- = 1 / 3
  calc f (f (logb 3 2)) = f ((3 ^ logb 3 2 - 4) / 3 ^ logb 3 2) := by rw [hfpos _ (logb_pos (by simp) (by simp))]
                      _ = f ((2 - 4) / 2) := by rw [rpow_logb (by norm_num) (by norm_num) (by norm_num)]
                      _ = f (-1) := by norm_num
                      _ = -f 1 := hodd 1
                      _ = -((3 ^ (1 : ℝ) - 4) / 3 ^ (1 : ℝ)) := by rw [hfpos _ (by norm_num)]
                      _ = 1 / 3 := by norm_num
