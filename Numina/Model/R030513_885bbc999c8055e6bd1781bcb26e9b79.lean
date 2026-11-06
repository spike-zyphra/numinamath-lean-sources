import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_110417 (E : ℝ → ℝ → ℝ)
  (hE : E = λ a b => a + b + 1 / (a * b)) :
  IsLeast {x | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ a + b ≤ 1 ∧ E a b = x} 5 := by
  constructor
  · -- Show that 5 is in the set
    use 1 / 2, 1 / 2
    constructor
    · -- Show that 1/2 > 0
      norm_num
    constructor
    · -- Show that 1/2 > 0
      norm_num
    constructor
    · -- Show that 1/2 + 1/2 ≤ 1
      norm_num
    · -- Show that E (1/2) (1/2) = 5
      rw [hE]
      norm_num
  · -- Show that 5 is the least element in the set
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h1, heq⟩
    rw [hE] at heq
    have h2 : a * b > 0 := by
      apply mul_pos
      all_goals linarith
    have h3 : a + b + 1 / (a * b) ≥ 5 := by
      have h4 : a * b > 0 := h2
      have eq1 : a + b + 1 / (a * b) - 5 ≥ 0 := by
        have eq2 : a + b + 1 / (a * b) - 5 = ((a + b) * (a * b) + 1 - 5 * (a * b)) / (a * b) := by
          field_simp
          <;> ring
        rw [eq2]
        apply div_nonneg
        · -- Show that numerator is non-negative
          nlinarith [sq_nonneg (a - b), sq_nonneg ((a + b) - 1), sq_nonneg (a * b - 1 / 4), mul_pos ha hb, sq_nonneg (a + b - 1),
            sq_nonneg (a - b), sq_nonneg (a^2 * b - a * b^2), sq_nonneg (4 * a * b - 1), mul_self_nonneg (a - b), mul_self_nonneg (a + b - 1),
            mul_pos ha hb]
        · -- Show that denominator is positive
          positivity
      linarith
    have hx2 : a + b + 1 / (a * b) = x := by
      linarith [heq]
    linarith [h3, hx2]