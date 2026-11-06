import Mathlib

open Real
open scoped BigOperators

theorem algebra_114426 :
  IsLeast {x | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 8 ∧ x = a + b + c} 6 := by
  constructor
  · -- Show that 6 is in the set
    use 2, 2, 2
    norm_num
  · -- Show that no value smaller than 6 is in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, hx⟩
    have h2 : a + b + c ≥ 6 := by
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    linarith [h2, hx]