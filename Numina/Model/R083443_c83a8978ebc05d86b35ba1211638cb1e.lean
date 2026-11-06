import Mathlib

theorem algebra_300182 (f : ℝ → ℝ) (hf : f = fun x => x^3 - 3 * x) :
    IsGreatest {y | ∃ x, y = f x ∧ x^4 + 36 ≤ 13 * x^2} 18 := by
  constructor
  · -- Show that 18 is achievable, witness is x = 3
    use 3
    constructor
    · -- Show that f(3) = 18
      rw [hf]
      norm_num
    · -- Show that 3 satisfy the constraint
      norm_num
  · -- Show that any value in the set is less than or equal to 18
    intro y hy
    rcases hy with ⟨x, hx1, hx2⟩
    rw [hf] at hx1
    simp at hx1
    -- Show constraint
    nlinarith [sq_nonneg (x^2 - 9 : ℝ), sq_nonneg (x^2 - 4 : ℝ), sq_nonneg (x^2 - 1 : ℝ),
      sq_nonneg (x - 3 : ℝ), sq_nonneg (x + 3 : ℝ), sq_nonneg (x - 2 : ℝ), sq_nonneg (x + 2 : ℝ),
      sq_nonneg ((x)^2 - 2 : ℝ), sq_nonneg ((x)^2 - 3 : ℝ),
      sq_nonneg (x^2 - 2 : ℝ), sq_nonneg (x^2 - 3 : ℝ)]