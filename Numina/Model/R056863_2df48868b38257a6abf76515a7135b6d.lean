import Mathlib

theorem algebra_149936 {x : ℕ} (hx : x ≠ 0) (h1 : (3 / 8 : ℚ) * x + 50 = (5 / 7 : ℚ) * (x - (3 / 8 : ℚ) * x - 50)) :
    x - (3 / 8 : ℚ) * x - 50 = 700 := by
  have eq1 : (x : ℚ) > (0 : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero hx
  have h2 : (x : ℚ) = 1200 := by
    linarith
  rw [h2]
  norm_num