import Mathlib

open Real

theorem inequalities_4146 : IsGreatest {x : ℝ | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 8 ∧ x = 1 / (2 * a + b + 6) + 1 / (2 * b + c + 6) + 1 / (2 * c + a + 6)} (1 / 4) := by
  constructor
  · -- Show that 1/4 is in the set
    use 2, 2, 2
    norm_num
  · -- Show that 1/4 is greatest
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, habc, hx⟩
    have h1 : 0 < (2 * a + b + 6) * (2 * b + c + 6) * (2 * c + a + 6) := by
      positivity
    have h2 : 1 / (2 * a + b + 6) + 1 / (2 * b + c + 6) + 1 / (2 * c + a + 6) ≤ 1 / 4 := by
      have h7 : (1 / (2 * a + b + 6) + 1 / (2 * b + c + 6) + 1 / (2 * c + a + 6) ) - 1 / 4 ≤ 0 := by
        have h8 : (1 / (2 * a + b + 6) + 1 / (2 * b + c + 6) + 1 / (2 * c + a + 6) ) - 1 / 4 =
            ( (2 * b + c + 6) * (2 * c + a + 6) * 4 + (2 * a + b + 6) * (2 * c + a + 6) * 4 + (2 * a + b + 6) * (2 * b + c + 6) * 4 - (2 * a + b + 6) * (2 * b + c + 6) * (2 * c + a + 6) ) / ( (2 * a + b + 6) * (2 * b + c + 6) * (2 * c + a + 6) * 4 ) := by
          field_simp
          ring
        rw [h8] at *
        apply div_nonpos_of_nonpos_of_nonneg
        · -- Show numerator ≤ 0
          nlinarith [sq_nonneg (a - 2 : ℝ), sq_nonneg (b - 2 : ℝ), sq_nonneg (c - 2 : ℝ),
            sq_nonneg (a * b - 4 : ℝ), sq_nonneg (a * c - 4 : ℝ), sq_nonneg (b * c - 4 : ℝ),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (show 0 < a * b by nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]) (show 0 < a * c by nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc])
          ]
        · -- Show denominator ≥ 0
          positivity
      linarith
    linarith [h2, hx]