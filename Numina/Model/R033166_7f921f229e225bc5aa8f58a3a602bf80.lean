import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_278852 :
  IsLeast {x | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 ∧ x = 1 / a + 4 / b + 9 / c} 36 := by
  constructor
  · -- Show that 36 is in the set
    use 1 / 6, 1 / 3, 1 / 2
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    norm_num
  · -- Show that no smaller element is in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, hx⟩
    have h2 : 1 / a + 4 / b + 9 / c ≥ 36 := by
      have h3 : a + b + c = 1 := h1
      have h4 : a * b * c > 0 := by
        apply mul_pos
        apply mul_pos
        all_goals linarith
      have h5 : 1 / a + 4 / b + 9 / c - 36 ≥ 0 := by
        have h6 : 1 / a + 4 / b + 9 / c - 36 =
            (b * c + 4 * a * c + 9 * a * b - 36 * a * b * c) / (a * b * c) := by
          field_simp
          ring
        rw [h6]
        have h7 : b * c + 4 * a * c + 9 * a * b - 36 * a * b * c ≥ 0 := by
          nlinarith [sq_nonneg (a - 1 / 6), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 2), 
            h3, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith [h2, hx]