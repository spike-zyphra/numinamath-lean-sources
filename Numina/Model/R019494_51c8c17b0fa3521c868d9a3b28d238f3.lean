import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_156195 :
  IsLeast {x | ∃ a b c : ℝ, a + b + c = 5 ∧ 1 ≤ a ∧ a ≤ 2 ∧ 1 ≤ b ∧ b ≤ 2 ∧ 1 ≤ c ∧ c ≤ 2 ∧ x = 1 / (a + b) + 1 / (b + c)} (4 / 7) := by
  constructor
  · -- Show 4/7 is in the set.
    use 3 / 2, 2, 3 / 2
    norm_num
  · -- Show that 4/7 is the minimum of the set
    intro x hx
    rcases hx with ⟨a, b, c, h1, h2, h3, h4, h5, h6, h7, h8⟩
    have h8' : 1 / (a + b) + 1 / (b + c) ≥ 4 / 7 := by
      have h11 : 0 < a + b := by
        nlinarith
      have h12 : 0 < b + c := by
        nlinarith
      have h13 : 0 < (a + b) * (b + c) := by
        positivity
      have h14 : 1 / (a + b) + 1 / (b + c) - 4 / 7 ≥ 0 := by
        have h15 : 1 / (a + b) + 1 / (b + c) - 4 / 7 = (7 * ( (b + c) + (a + b) ) - 4 * ( (a + b) * (b + c) ) ) / (7 * ( (a + b) * (b + c) ) ) := by
          field_simp
          <;> ring
        rw [h15] at *
        apply div_nonneg
        nlinarith [mul_self_nonneg (a - c), mul_self_nonneg (b - 1.5), sq_nonneg (a - 2), sq_nonneg (c - 2), sq_nonneg (b - 2), mul_nonneg (show (0 : ℝ) ≤ a - 1 by linarith) (show (0 : ℝ) ≤ c - 1 by linarith), mul_nonneg (show (0 : ℝ) ≤ a - 1 by linarith) (show (0 : ℝ) ≤ b - 1 by linarith), mul_nonneg (show (0 : ℝ) ≤ b - 1 by linarith) (show (0 : ℝ) ≤ c - 1 by linarith) ]
        all_goals positivity
      linarith
    linarith [h8, h8']