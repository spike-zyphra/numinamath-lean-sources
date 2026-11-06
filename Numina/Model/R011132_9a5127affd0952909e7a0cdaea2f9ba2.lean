import Mathlib

theorem algebra_220609 :
    IsGreatest {y : ℝ | 0 < y ∧ ∃ x, 0 < x ∧ x ^ 3 + y ^ 3 = (4 * x - 5 * y) * y} (1 / 3) := by
  constructor
  · -- Show 1/3 is in the set and the second
    constructor
    · norm_num
    use 2 / 3
    constructor
    · norm_num
    · norm_num
  · -- Show any y in the set is at most 1/3.
    intro y ⟨hy_pos, x, hx_pos, heq⟩

    have heq2 : x ^ 3 + y ^ 3 + 5 * y ^ 2 - 4 * x * y = 0 := by
      have h1 : x ^ 3 + y ^ 3 = (4 * x - 5 * y) * y := heq
      have h2 : (4 * x - 5 * y) * y = 4 * x * y - 5 * y ^ 2 := by
        ring
      rw [h2] at h1
      linarith

    nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (y - 1 / 3), sq_nonneg (x - 2 * y), sq_nonneg (x + 2 * y - 4 / 3),
          sq_nonneg (x - 2 * y), sq_nonneg (x - 4 / 3), sq_nonneg (y - 1 / 3), 
          mul_pos hx_pos hy_pos, sq_nonneg (x - 2), sq_nonneg (y - 1 / 3)]