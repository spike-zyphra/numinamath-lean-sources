import Mathlib

open Real

theorem inequalities_312009 :
    IsLeast {x | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ (1 + a) * (1 + b) * (1 + c) = 8 ∧ x = a * b * c + 9 / (a * b * c)} 10 := by
  constructor
  · -- Show that 10 is achievable by setting a = b = c = 1
    use 1, 1, 1
    norm_num
  · -- Now, we need to show that 10 is the minimum
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h, hx⟩
    have h1 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h2 : a * b * c + 9 / (a * b * c) ≥ 10 := by
      have h1' : a * b * c > 0 := h1
      have h3 : a * b * c + 9 / (a * b * c) - 10 ≥ 0 := by
        have pos1 : a * b * c > 0 := h1'
        have pos2 : a * b * c + 9 / (a * b * c) - 10 = ( (a * b * c) ^ 2 + 9 - 10 * (a * b * c) ) / (a * b * c) := by
          field_simp
          <;> ring
        rw [pos2] at *
        apply div_nonneg
        · -- Show that the numerator is non-negative
          nlinarith [sq_nonneg (a * b * c - 1), sq_nonneg (a * b * c - 9), 
            sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
            h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
        · -- Show that the denominator is non-negative
          linarith
      linarith
    linarith [hx, h2]