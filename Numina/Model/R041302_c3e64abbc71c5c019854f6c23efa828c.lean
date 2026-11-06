import Mathlib

open Real

theorem inequalities_203935 :
  IsLeast {S : ℝ | ∃ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ a * b * c = 1 ∧
  S = 1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1)} 1 := by
  constructor
  · -- Show that 1 is in the set.
    use 1, 1, 1
    norm_num
  · -- Show that 1 is the least element in the set.
    intro S hS
    rcases hS with ⟨a, b, c, ha, hb, hc, habc, hS⟩
    have h1 : 1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) ≥ 1 := by
      have h3 : 0 < (2 * a + 1) * (2 * b + 1) * (2 * c + 1) := by positivity
      have h4 : 1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) - 1 ≥ 0 := by
        have h5 : 1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) - 1 =
          ( (2 * b + 1) * (2 * c + 1) + (2 * a + 1) * (2 * c + 1) + (2 * a + 1) * (2 * b + 1) - (2 * a + 1) * (2 * b + 1) * (2 * c + 1) ) / ( (2 * a + 1) * (2 * b + 1) * (2 * c + 1) ) := by
          field_simp
          ring
        rw [h5] at *
        apply div_nonneg
        have h7 : (2 * b + 1) * (2 * c + 1) + (2 * a + 1) * (2 * c + 1) + (2 * a + 1) * (2 * b + 1) - (2 * a + 1) * (2 * b + 1) * (2 * c + 1) ≥ 0 := by
          nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
            sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
            habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
        linarith
        all_goals positivity
      linarith
    linarith [hS, h1]