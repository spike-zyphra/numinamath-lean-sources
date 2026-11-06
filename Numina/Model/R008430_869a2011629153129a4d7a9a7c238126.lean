import Mathlib

theorem algebra_9298 : IsGreatest {z : ℝ | ∃ x y, z = 2 * x + 3 * y ∧ 0 ≤ x ∧ 0 ≤ y ∧
      x + y - 3 ≤ 0 ∧ 0 ≤ 2 * x + y - 4} 8 := by

  constructor
  · use 1, 2
    norm_num
  · intro z hz
    rcases hz with ⟨x, y, hz_eq, hx, hy, h1, h2⟩
    nlinarith