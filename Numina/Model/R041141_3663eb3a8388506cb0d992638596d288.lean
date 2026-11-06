import Mathlib

theorem algebra_305621 : 
    IsGreatest {z : ℝ | ∃x y, x + y + z = 5 ∧ x * y + y * z + z * x = 3} (13 / 3) := by
  constructor
  · -- Show 13/3 is in the set
    use 1 / 3, 1 / 3
    constructor
    · norm_num
    · norm_num
  · -- Show 13/3 is greatest
    intro z h
    rcases h with ⟨x, y, h1, h2⟩
    have h3 : x + y = 5 - z := by linarith
    have h4 : x * y = z ^ 2 - 5 * z + 3 := by
      have h5 : x * y + y * z + z * x = 3 := h2
      have h6 : x * y + z * (x + y) = 3 := by
        linarith
      rw [h3] at h6
      linarith
    have h7 : (x + y) ^ 2 ≥ 4 * (x * y) := by
      linarith [sq_nonneg (x - y)]
    rw [show (x + y) ^ 2 = (5 - z) ^ 2 by rw [h3]] at h7
    rw [show 4 * (x * y) = 4 * (z ^ 2 - 5 * z + 3) by rw [h4]] at h7
    nlinarith [sq_nonneg (z - 13 / 3), sq_nonneg (z + 1)]