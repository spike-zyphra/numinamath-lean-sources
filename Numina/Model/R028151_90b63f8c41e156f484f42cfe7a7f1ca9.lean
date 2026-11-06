import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_132437 :
  IsLeast {x : ℝ | ∃ a b c d : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
    a + 2 * b = 1 ∧ c + 2 * d = 1 ∧ x = 1 / a + 1 / (b * c * d)} 25 := by

  constructor
  · -- Show 25 is in the set with the given values
    use (1 / 5), (2 / 5), (1 / 2), (1 / 4)
    norm_num
  · -- Show 25 is the minimum element in the set
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, ha2b, hc2d, hx⟩
    have h1 : 0 < a := by linarith
    have h2 : 0 < b := by linarith
    have h3 : 0 < c := by linarith
    have h4 : 0 < d := by linarith
    have h5 : 1 / a + 1 / (b * c * d) ≥ 25 := by
      have h6 : 0 < a * b * c * d := by positivity
      have h7 : 1 / a + 1 / (b * c * d) - 25 ≥ 0 := by
        have h8 : a * b * c * d > 0 := by positivity
        have h9 : 1 / a + 1 / (b * c * d) - 25 = (b * c * d + a - 25 * (a * b * c * d)) / (a * (b * c * d)) := by
          field_simp
          <;> ring
        rw [h9] at *
        apply div_nonneg
        -- Prove the numerator is non-negative using inequality
        nlinarith [sq_nonneg (a - 1 / 5), sq_nonneg (b - 2 / 5), sq_nonneg (c - 1 / 2), sq_nonneg (d - 1 / 4),
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
          ha2b, hc2d]
        -- Prove the denominator is positive
        positivity
      linarith
    linarith [hx, h5]