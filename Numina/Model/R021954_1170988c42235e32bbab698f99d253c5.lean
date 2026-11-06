import Mathlib

theorem algebra_178141 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x * 7 = y * 3) (h2 : x * 12 = y * 9) :
    x / y = 35 / 12 := by 
  -- From h1: $x \cdot 7 = y \cdot 3$ 
  -- From h2: $x \cdot 12 = y \cdot 9$ 
  -- This system is contradictory.
  have h3 : y = 0 := by
    linarith [h1, h2]
  -- But hypothesis hy: $y > 0$ and y = 0 contradicts
  -- Substitute y = 0 into hypothesis h3 which contradicts h3 > 0
  have h4 : y > 0 := hy
  rw [show y = 0 by linarith [h1, h2]] at h4
  all_goals linarith