import Mathlib

theorem algebra_8942 :
  IsLeast {x | ∃ a b : ℝ, x = 2 * a ^ 2 - 4 * a * b + 7 * b ^ 2 - 4 * a - 6 * b + 2020} 2013 := by
  constructor
  · -- First, we need to show that 2013 is in the set
    use 2, 1
    norm_num
  · -- Now, we need to prove that no smaller value is in the set
    intro x hx
    rcases hx with ⟨a, b, h⟩
    have h1 : 2 * a ^ 2 - 4 * a * b + 7 * b ^ 2 - 4 * a - 6 * b + 2020 ≥ 2013 := by
      nlinarith [sq_nonneg (a - (b + 1)), sq_nonneg (b - 1)]
    linarith