import Mathlib

open Real

theorem inequalities_319311 :
    IsLeast {x | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1 ∧ x = a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1))} (3 / 4) := by
  constructor
  · -- First, let's prove 3/4 is in the set.
    use 1, 1, 1
    norm_num
  · -- Now, prove that 3/4 is minimum.
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, habc, hx⟩
    have h1 : a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1)) ≥ 3 / 4 := by
      have h2 : a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1)) - 3 / 4 ≥ 0 := by
        have h21 : a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1)) - 3 / 4 =
          (4 * a * (c + 1) + 4 * b * (a + 1) + 4 * c * (b + 1) - 3 * (a + 1) * (b + 1) * (c + 1)) / (4 * (a + 1) * (b + 1) * (c + 1)) := by
          field_simp
          ring
        rw [h21] at *
        apply div_nonneg
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
                  sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc
                  ]
        positivity
      linarith
    linarith [h1, hx]