import Mathlib

theorem algebra_16379 :
  IsGreatest {7 * x + 2 * y + 8 * z | (x : ℝ) (y : ℝ) (z : ℝ) (h : 4 * x ^ 2 + y ^ 2 + 16 * z ^ 2 = 1)} (9 / 2) := by
  constructor
  · -- First, we will show that 9/2 is in the set.
    use 7 / 18, 4 / 9, 1 / 9
    norm_num
  · -- Now, we have to prove that no value greater than 9/2 is in the set.
    intro w
    rintro ⟨x, y, z, h, rfl⟩
    nlinarith [sq_nonneg (x - 7 / 18), sq_nonneg (y - 4 / 9), sq_nonneg (z - 1 / 9),
      sq_nonneg (2 * x - 7 / 9), sq_nonneg (y - 4 / 9), sq_nonneg (4 * z - 4 / 9),
      h, mul_self_nonneg (2 * x), mul_self_nonneg (y), mul_self_nonneg (4 * z)]