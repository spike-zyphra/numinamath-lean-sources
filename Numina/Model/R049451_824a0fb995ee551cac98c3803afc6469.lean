import Mathlib

theorem algebra_308729 :
    IsGreatest {z : ℝ | ∃ x y, x + y + z = 5 ∧ x * y + y * z + z * x = 3} (13 / 3) := by
  constructor
  · -- Show that there exist x y such that z = 13 / 3 is in the set
    use 1 / 3, 1 / 3
    constructor
    · -- Check that 1/3 + 1/3 + 13/3 = 5
      norm_num
    · -- Check that 1/3 * 1/3 + 1/3 * 13/3 + 13/3 * 1/3 = 3
      norm_num
  · -- Show that for any z in the set, z ≤ 13 / 3
    intro z hz
    rcases hz with ⟨x, y, h1, h2⟩
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2 / 3), sq_nonneg (z - 13 / 3), sq_nonneg (z + 1), sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3)]