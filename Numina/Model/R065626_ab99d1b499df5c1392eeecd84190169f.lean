import Mathlib

theorem algebra_104858 {x y : ℤ} (h₀ : x + y = 86) (h₁ : (x - 9) * 9 = 8 * (y - 9)) :
    x / y = 41 / 45 := by
  have eq1 : y = 86 - x := by
    linarith
  rw [eq1] at h₁
  have hx : x = 41 := by 
    linarith
  have hy : y = 45 := by
    rw [hx] at h₀
    linarith
  rw [hx, hy]
  all_goals norm_num