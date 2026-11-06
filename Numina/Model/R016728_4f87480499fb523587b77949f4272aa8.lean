import Mathlib

theorem algebra_326649 :
    IsGreatest {M : ℝ | ∃ x y z, M = x * y + 2 * y * z + 3 * x * z ∧ x + y + z = 1} (3 / 4) := by
  constructor
  · -- Show 3/4 is in the set.
    use 1 / 2, (0 : ℝ), 1 / 2
    constructor
    · -- Verify M = 3/4
      norm_num
    · -- Verify x + y + z = 1
      norm_num
  · -- Show 3/4 is the greatest in the set.
    intro M hM
    rcases hM with ⟨x, y, z, h1, h2⟩
    have hz : z = 1 - x - y := by linarith
    rw [hz] at h1
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 0), sq_nonneg ((1 - x - y) - 1 / 2), sq_nonneg (x + y - 1 / 2), sq_nonneg (y - 0), sq_nonneg ((1 - x - y) - 1 / 2)]