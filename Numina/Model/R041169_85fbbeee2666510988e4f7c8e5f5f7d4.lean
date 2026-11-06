import Mathlib

open Real

theorem algebra_2720 :
    IsLeast {x | ∃ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 3 ∧ x = a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c} (9 / 2) := by
  constructor
  · -- Show that 9/2 is in the set
    use 3 / 2, 3 / 2, 0
    norm_num
  · -- Show that 9/2 is minimal
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, hx⟩
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a - 3 / 2), sq_nonneg (b - 3 / 2), sq_nonneg (c - 3 / 2),
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc
        ]