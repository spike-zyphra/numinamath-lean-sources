import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_142120 (m : ℝ) (hm : m ≠ 0)
  (f : ℝ → ℝ)
  (hf : f = λ x => (1 + m^2) / m^2 * x^2 - 2 * (1 + m^2) / m * x - 1) :
  IsLeast {y | ∃ x, f x = y} (-2 - m^2) := by
  constructor
  · -- Show that -2 - m ^ 2 is in the image of f.
    use m
    rw [hf]
    field_simp
    ring
  · -- Show that -2 - m^2 is minimal in the image of f.
    intro y
    rintro ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    have h1 : (1 + m^2) / m^2 * x^2 - 2 * (1 + m^2) / m * x - 1 ≥ -2 - m^2 := by
      have h4 : (1 + m^2) / m^2 * (x - m) ^ 2 ≥ 0 := by
        apply mul_nonneg
        -- Show $\frac{1 + m^2}{m^2} \geq 0$.
        have h3 : (1 + m^2) / m^2 ≥ 0 := by
          have hm2_pos : m^2 > 0 := by
            exact sq_pos_of_ne_zero hm
          have h4 : 1 + m^2 > 0 := by
            nlinarith [sq_pos_of_ne_zero hm]
          apply div_nonneg
          linarith
          linarith
        linarith
        -- Show $(x - m)^2 \geq 0$.
        apply pow_two_nonneg
      have eq1 : (1 + m^2) / m^2 * x^2 - 2 * (1 + m^2) / m * x - 1 = (1 + m^2) / m^2 * (x - m) ^ 2 + (-2 - m^2) := by
        field_simp
        ring
      linarith [eq1, h4]
    linarith