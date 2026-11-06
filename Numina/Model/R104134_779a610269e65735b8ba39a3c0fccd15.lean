import Mathlib

theorem algebra_93065 :
    IsGreatest {z : ℝ | ∃ x y, z = 3 * x + 4 * y ∧ x ^ 2 + y ^ 2 = 14 * x + 6 * y + 6} 73 := by
  constructor
  · -- Show that 73 is achievable, using x = 59/5 and y = 47/5
    use 59 / 5, 47 / 5
    constructor
    · -- Verify 3 * (59/5) + 4 * (47/5) = 73
      norm_num
    · -- Verify (59/5)^2 + (47/5)^2 = 14 * (59/5) + 6 * (47/5) + 6
      norm_num
  · -- Show that 73 is an upper bound
    intro z hz
    rcases hz with ⟨x, y, hz, hx2⟩
    -- Show that z = 3x + 4y and x^2 + y^2 = 14x + 6y + 6 implies z ≤ 73
    have h1 : (x - 7) ^ 2 + (y - 3) ^ 2 = 64 := by
      nlinarith
    nlinarith [sq_nonneg (x - 59 / 5), sq_nonneg (y - 47 / 5)]