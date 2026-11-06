import Mathlib

theorem algebra_306376 :
    IsLeast {x | ∃ a b : ℝ, x = 5 * a ^ 2 + 4 * b ^ 2 - 8 * a * b + 2 * a + 4} 3 := by
  constructor
  · -- Show 3 is in the set
    use -1, -1
    norm_num
  · -- Show 3 is minimal
    intro x hx
    rcases hx with ⟨a, b, h⟩
    have h1 : 5 * a ^ 2 + 4 * b ^ 2 - 8 * a * b + 2 * a + 4 ≥ 3 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + 1), sq_nonneg (a - b), sq_nonneg (a - (-1)), sq_nonneg (b - (-1))]
    linarith [h, h1]