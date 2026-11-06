import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_600124 :
  IsLeast {x | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c ≤ 3 / 2 ∧ x = a * b * c + 1 / (a * b * c)} (65 / 8) := by
  constructor
  · -- Show that 65/8 is in the set.
    use 1 / 2, 1 / 2, 1 / 2
    norm_num
  · -- Show that 65/8 is the minimum of the set.
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h, hx⟩
    -- Establish that a * b * c ≤ 1 / 8 using nonlinear arithmetic.
    have h1 : a * b * c ≤ 1 / 8 := by
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2),
          sq_nonneg (a * b - 1 / 4), sq_nonneg (b * c - 1 / 4), sq_nonneg (c * a - 1 / 4),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]
    -- Show a * b * c > 0.
    have h2 : a * b * c > 0 := mul_pos (mul_pos ha hb) hc
    -- Show a * b * c + 1 / (a * b * c) ≥ 65 / 8.
    have h3 : a * b * c + 1 / (a * b * c) ≥ 65 / 8 := by
      -- Use nonlinear arithmetic.
      have h4 : a * b * c ≤ 1 / 8 := h1
      have h5 : a * b * c > 0 := h2
      have h6 : (a * b * c) + 1 / (a * b * c) - 65 / 8 ≥ 0 := by
        -- Rewrite the expression to a common denominator.
        have h8 : (a * b * c) + 1 / (a * b * c) - 65 / 8 = (8 * (a * b * c) ^ 2 - 65 * (a * b * c) + 8) / (8 * (a * b * c)) := by
          field_simp
          ring
        rw [h8] at *
        have h9 : 8 * (a * b * c) ^ 2 - 65 * (a * b * c) + 8 ≥ 0 := by
          nlinarith [sq_nonneg ((a * b * c) - 1 / 8), sq_nonneg ((a * b * c) - 8),
            h4, mul_pos h2 (show (a * b * c) > 0 by linarith)]
        apply div_nonneg
        · linarith
        · positivity
      linarith
    -- Rewrite x to the expression and apply the lower bound.
    rw [hx] at *
    linarith [h3, h1]