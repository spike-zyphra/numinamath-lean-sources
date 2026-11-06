import Mathlib

theorem algebra_161470 :
    ∃ b c d : ℚ, ∃ f : ℚ → ℚ, ∀ x : ℚ, f x = x ^ 3 + b * x ^ 2 + c * x + d ∧
      ∃ x1 x2 x3 : ℚ, x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x1 ∧ f x1 = 0 ∧ f x2 = 0 ∧ f x3 = 0 ∧
      ∃ x4 x5 : ℚ, x4 ≠ x5 ∧ deriv f x4 = 0 ∧ deriv f x5 = 0 := by

  use -13 / 8
  use 5 / 8
  use (0 : ℚ)
  use fun x => x ^ 3 + (-13 / 8) * x ^ 2 + (5 / 8) * x + (0 : ℚ)
  intro x
  constructor
  · -- Show that f x = x^3 + b*x^2 + c*x + d
    simp
  · -- Show the existence of three distinct rational roots
    use (0 : ℚ)
    use (1 : ℚ)
    use (5 / 8 : ℚ)
    constructor
    · -- Show x1 ≠ x2
      norm_num
    constructor
    · -- Show x2 ≠ x3
      norm_num
    constructor
    · -- Show x3 ≠ x1
      norm_num
    constructor
    · -- Show f x1 = 0
      norm_num
    constructor
    · -- Show f x2 = 0
      norm_num
    constructor
    · -- Show f x3 = 0
      norm_num
    · -- Show the existence of two distinct rational extrema
      use (1 / 4 : ℚ)
      use (5 / 6 : ℚ)
      constructor
      · -- Show x4 ≠ x5
        norm_num
      constructor
      · -- Show deriv f x4 = 0
        simp [deriv_pow, deriv_const, deriv_add, deriv_sub, mul_comm]
        all_goals norm_num
      · -- Show deriv f x5 = 0
        simp [deriv_pow, deriv_const, deriv_add, deriv_sub, mul_comm]
        all_goals norm_num