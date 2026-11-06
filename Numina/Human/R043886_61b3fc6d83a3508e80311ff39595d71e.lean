import Mathlib

open Real

theorem inequalities_103130 :
    IsGreatest {x | ∃ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a^2 + b^2 + c^2 + a * b * c ≤ 4 ∧ x = a + b + c + a * b * c} 4 := by

  constructor
  · -- First part: Prove that 4 belongs to the set (i.e., it's attainable)
    use 1, 1, 1
    norm_num

  · -- Second part: Prove that 4 is the greatest element in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, hx⟩
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]