import Mathlib

open Real Set

theorem algebra_273530 :
    IsLeast {n | ∃ x y : ℝ, n = (x + 3)^2 + 2 * (y - 2)^2 + 4 * (x - 7)^2 + (y + 4)^2} 104 := by 
  constructor
  · -- Show that 104 belongs to the set
    use 5, 0
    norm_num
  · -- Show that 104 is the least element in the set
    intro n hn
    rcases hn with ⟨x, y, h⟩
    -- Simplify the given expression by completing the square
    have h1 : (x + 3) ^ 2 + 2 * (y - 2) ^ 2 + 4 * (x - 7) ^ 2 + (y + 4) ^ 2 ≥ 104 := by
      nlinarith [sq_nonneg (x - 5 : ℝ), sq_nonneg (y : ℝ), sq_nonneg (5 * (x - 5)), sq_nonneg (3 * y)]
    linarith [h, h1]