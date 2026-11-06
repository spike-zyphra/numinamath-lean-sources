import Mathlib

open Real
open scoped BigOperators

theorem algebra_601523 :
  IsLeast {x | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a ∧ a + b + c = 3 ∧ x = a^2 + b^2 + c^2 + 4/3 * a * b * c} (13/3) := by

  constructor
  · -- Show that 13/3 is in the set.
    use 1, 1, 1
    norm_num

  · -- Show that 13/3 is the least element.
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, h2, h3, h4, hx⟩

    have h5 : a ^ 2 + b ^ 2 + c ^ 2 + 4 / 3 * a * b * c ≥ 13 / 3 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
        mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), -- up here
        mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3),
        mul_pos (sub_pos.mpr h1) (sub_pos.mpr h3)]
    linarith [h5, hx]