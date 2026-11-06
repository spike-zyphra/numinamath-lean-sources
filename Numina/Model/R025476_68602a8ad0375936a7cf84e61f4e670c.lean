import Mathlib

theorem algebra_3146 :
  IsLeast {z : ℝ | ∃ x y : ℝ, x < 0 ∧ y < 0 ∧ z = 13 * x ^ 2 + 16 * x * y + 61 * y ^ 2 + 12 * x + 24 * y + 4} 0 := by
  constructor
  · -- Show that 0 is in the set
    use -10 / 27, -4 / 27
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 0 is the least element in the set
    intro z h
    rcases h with ⟨x, y, hx, hy, h_eq⟩
    have h : 13 * x ^ 2 + 16 * x * y + 61 * y ^ 2 + 12 * x + 24 * y + 4 ≥ (0 : ℝ) := by
      nlinarith [sq_nonneg (x + 10 / 27), sq_nonneg (y + 4 / 27),
        sq_nonneg (13 * (x + 10 / 27) + 16 * (y + 4 / 27)), 
        sq_nonneg (16 * (x + 10 / 27) + 122 * (y + 4 / 27)), 
        mul_pos (show (0 : ℝ) < 27 by norm_num) (show (0 : ℝ) < 27 by norm_num)]
    linarith [h_eq, h]