import Mathlib

theorem algebra_227616 :
    IsLeast {z : ℝ | ∃ x y, z = 6 * y + 8 * x - 9 ∧ x ^ 2 + y ^ 2 + 25 = 10 * (x + y)} 11 := by
  constructor
  · -- Show that 11 is in the set
    use 1, 2
    constructor
    · -- Show that 6 * 2 + 8 * 1 - 9 = 11
      norm_num
    · -- Show that 1^2 + 2^2 + 25 = 10 * (1 + 2)
      norm_num
  · -- Show that z ≥ 11 for any z in the set
    intro z h
    rcases h with ⟨x, y, h_eq, h_ellipse⟩
    have h1 : (x - 5) ^ 2 + (y - 5) ^ 2 = 25 := by 
      nlinarith
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 2), 
      sq_nonneg (x - 5 - 4 * (x - 1)), sq_nonneg (y - 5 - 3 * (y - 2)), 
      sq_nonneg (8 * (x - 1) + 6 * (y - 2))]