import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_272154 :
  IsLeast {x | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ x = (a^2 + b^2 + 2) * (1 / (a + b) + 1 / (a * b + 1))} 4 := by
  constructor
  · -- Show that 4 is achievable, using a = 1, b = 1
    use 1, 1
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 4 is the least element in the set
    intro x hx
    rcases hx with ⟨a, b, ha, hb, heq⟩
    have h : (a^2 + b^2 + 2) * (1 / (a + b) + 1 / (a * b + 1)) ≥ 4 := by
      have h1 : a + b > 0 := by linarith
      have h2 : a * b + 1 > 0 := by nlinarith
      have h3 : (a^2 + b^2 + 2) * ( (a * b + 1) + (a + b) ) - 4 * (a + b) * (a * b + 1) ≥ 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a * b - 1), sq_nonneg (a * b - a),
          sq_nonneg (a * b - b), mul_pos ha hb]
      have h4 : (a^2 + b^2 + 2) * (1 / (a + b) + 1 / (a * b + 1)) - 4 ≥ 0 := by
        have h5 : (a^2 + b^2 + 2) * ( (a * b + 1) + (a + b) ) - 4 * (a + b) * (a * b + 1) ≥ 0 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a * b - 1), sq_nonneg (a * b - a),
            sq_nonneg (a * b - b), mul_pos ha hb]
        have h6 : (a^2 + b^2 + 2) * (1 / (a + b) + 1 / (a * b + 1)) - 4 =
            ( ( (a^2 + b^2 + 2) * ( (a * b + 1) + (a + b) ) - 4 * (a + b) * (a * b + 1) ) ) / ( (a + b) * (a * b + 1) ) := by
          field_simp [h1, h2]
          <;> ring
        rw [h6]
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith [h, heq]