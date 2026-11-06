import Mathlib

theorem algebra_161129 :
    IsLeast {x : ℝ | ∃(a b c d : ℝ), x = a * b - c * d ∧
        a^2 + b^2 + c^2 + d^2 = 21 ∧ 
        a + b + c + d = 9 ∧ a ≥ b ∧ b ≥ c ∧ c ≥ d} 2 := by 
  constructor
  · -- Show that 2 is in the set
    use 3, 2, 2, 2
    norm_num
  · -- Show that 2 is the minimum
    intro x hx
    rcases hx with ⟨a, b, c, d, heq, h1, h2, h3, h4, h5⟩
    nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a + b - c - d), sq_nonneg (b - c)]