import Mathlib

theorem algebra_5411 :
    IsGreatest {z : ℝ | ∃ x y, z = x ^ 2 + y ^ 2 + 12 * x - 16 * y ∧ x ^ 2 + y ^ 2 ≤ 25} 125 ∧
    IsLeast {z : ℝ | ∃ x y, z = x ^ 2 + y ^ 2 + 12 * x - 16 * y ∧ x ^ 2 + y ^ 2 ≤ 25} (-75) := by
  constructor
  · -- Show that 125 is greatest
    constructor
    · -- Show the existence of such x y
      use 3, -4
      norm_num
    · -- Show it's greatest
      intro z hz
      rcases hz with ⟨x, y, h_eq, h_le⟩
      nlinarith [sq_nonneg (x - 3), sq_nonneg (y + 4), sq_nonneg (x + 3), sq_nonneg (y - 4), sq_nonneg (x + 6), sq_nonneg (y - 8)]
  · -- Show that -75 is least
    constructor
    · -- Show the existence of such x y
      use -3, 4
      norm_num
    · -- Show it's least
      intro z hz
      rcases hz with ⟨x, y, h_eq, h_le⟩
      nlinarith [sq_nonneg (x + 3), sq_nonneg (y - 4), sq_nonneg (x - 3), sq_nonneg (y + 4), sq_nonneg (x + 6), sq_nonneg (y - 8)]