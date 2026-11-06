import Mathlib

theorem algebra_245349 :
    IsLeast {x | ∃ a b c d : ℝ, 5 * a + 6 * b - 7 * c + 4 * d = 1 ∧ x = 3 * a ^ 2 + 2 * b ^ 2 + 5 * c ^ 2 + d ^ 2} (15 / 782) := by

  constructor
  · -- Show that 15/782 is achievable
    use 25 / 782, 45 / 782, -21 / 782, 60 / 782
    constructor
    · -- Show that these satisfy the constraint
      norm_num
    · -- Show that the value is 15/782
      norm_num
  · -- Show that 15/782 is indeed the least
    intro x hx
    rcases hx with ⟨a, b, c, d, h1, h2⟩

    -- Use the method of Lagrange multipliers to establish the minimum
    nlinarith [sq_nonneg (a - 25 / 782), sq_nonneg (b - 45 / 782), sq_nonneg (c + 21 / 782), sq_nonneg (d - 60 / 782), mul_self_nonneg (a - 25 / 782), mul_self_nonneg (b - 45 / 782), mul_self_nonneg (c + 21 / 782), mul_self_nonneg (d - 60 / 782), h1]