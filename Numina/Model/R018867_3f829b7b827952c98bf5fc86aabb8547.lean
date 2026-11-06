import Mathlib

theorem algebra_597840 :
    IsGreatest {x | ∃ a b c d : ℝ, x = (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 + (b + d)^4 + (c + d)^4 ∧
      a^2 + b^2 + c^2 + d^2 ≤ 1} 6 := by 
  constructor
  · -- Show that 6 is in the set
    use 1 / 2, 1 / 2, 1 / 2, 1 / 2 
    norm_num
  · -- Show that 6 is the greatest 
    intro x hx
    rcases hx with ⟨a, b, c, d, h1, h2⟩
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
      sq_nonneg (a + b + c + d), sq_nonneg (a - b + c - d), sq_nonneg (a - b - c + d), sq_nonneg (a + b - c - d)]