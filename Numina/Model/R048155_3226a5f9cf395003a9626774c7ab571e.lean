import Mathlib

theorem algebra_70781 :
    {z : ℝ | ∃ x y : ℝ, 8 * y ^ 4 + 4 * x ^ 2 * y ^ 2 + 4 * x * y ^ 2 + 2 * x ^ 3 + 2 * y ^ 2 + 2 * x = x ^ 2 + 1 ∧ x + 2 * y ^ 2 = z} = {1 / 2} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, we show that any z in the image must be 1/2.
    rintro ⟨x, y, h_eq, h_eq2⟩
    nlinarith [sq_nonneg (x ^ 2 + 2 * y ^ 2 - 1 / 2), sq_nonneg (x + 2 * y^2 - 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (y ^ 2 - 1 / 4), sq_nonneg (x + 2 * y ^ 2), sq_nonneg (x + 2 * y^2 - 1 / 2), sq_nonneg (2 * y ^ 2 + x - 1 / 2), sq_nonneg (2 * y ^ 2 - 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (2 * y^2 - x), sq_nonneg (x^2 - 1/4)]
  · -- Now, we show that 1/2 is in the image.
    intro h
    rw [show z = 1 / 2 by linarith [h]]
    use 1 / 2, 0
    constructor
    · -- Verify the equation
      norm_num
    · -- Verify that x + 2 * y ^ 2 = z
      norm_num