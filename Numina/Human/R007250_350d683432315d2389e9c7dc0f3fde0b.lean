import Mathlib

theorem algebra_98485 {f : ℝ → ℝ} (h : ∀ x, f (3 * x - 1) = x ^ 2 + x + 1) : f 5 = 7 := by
    calc
     f 5 = f (3 * 2 - 1) := by norm_num
       _ = 2 ^2 + 2 + 1 := by rw [h 2]
       _ = 7 := by ring