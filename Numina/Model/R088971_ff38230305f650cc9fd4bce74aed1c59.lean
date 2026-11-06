import Mathlib

theorem algebra_110743 :
    IsLeast {x | ∃ a b c d : ℝ, x = a^2 + b^2 + c^2 + d^2 ∧ a + 2 * b + 3 * c + 4 * d = 12} (24 / 5) := by 
  constructor
  · -- Show that 24/5 is in the set
    use 2 / 5, 4 / 5, 6 / 5, 8 / 5
    constructor
    · norm_num
    · norm_num
  · -- Show that 24/5 is the least element in the set
    intro x hx
    rcases hx with ⟨a, b, c, d, h_eq, h_eq2⟩
    have h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ 24 / 5 := by
      nlinarith [sq_nonneg (a - 2 / 5), sq_nonneg (b - 4 / 5), sq_nonneg (c - 6 / 5), sq_nonneg (d - 8 / 5)]
    linarith