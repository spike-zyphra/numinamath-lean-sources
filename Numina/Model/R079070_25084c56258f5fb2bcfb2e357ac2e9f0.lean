import Mathlib

theorem algebra_305769 :
    IsLeast {x | ∃ a b : ℝ, x = a^2 + a * b + b^2 - a - 2 * b} (-1) := by
  constructor
  · -- Let's prove -1 is achievable
    use 0, 1
    norm_num
  · -- Let's prove -1 is a lower bound
    intro x hx
    rcases hx with ⟨a, b, h_eq⟩
    have h1 : a^2 + a * b + b^2 - a - 2 * b ≥ -1 := by
      nlinarith [sq_nonneg (a + b / 2 - 1 / 2), sq_nonneg (b - 1), sq_nonneg (a), sq_nonneg (b), 
                 sq_nonneg (a - 0), sq_nonneg (b - 1), 
                 sq_nonneg (a + b / 2), sq_nonneg (b), 
                 sq_nonneg (a - b), sq_nonneg (a + 2 * b)]
    linarith