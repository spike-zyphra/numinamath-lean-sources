import Mathlib

theorem algebra_307522 {x : ℕ} (hx : x = 3 * 36 + 3 * 44 + 10) : x = 250 := by
  calc 
    x = 3 * 36 + 3 * 44 + 10 := by rw [hx]
    _ = 108 + 132 + 10 := by norm_num
    _ = 250 := by norm_num