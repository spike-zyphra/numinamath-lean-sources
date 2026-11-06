import Mathlib

theorem algebra_599670 :
  IsGreatest {z : ℝ | ∃ x y, x + y + z = 5 ∧ x * y + y * z + z * x = 3} (13 / 3) := by
  constructor
  · -- Show that 13/3 is achievable, with x = y = 1/3
    use 1 / 3, 1 / 3
    norm_num
  · -- Show that for any z in the set, z ≤ 13/3
    intro z hz
    rcases hz with ⟨x, y, hsum, hprod⟩
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2 / 3), sq_nonneg (z - 13 / 3)]