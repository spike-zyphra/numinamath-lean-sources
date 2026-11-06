import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_319634 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
  (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ x y, f x y = (x^2 + y^2 + 2) * (1 / (x + y) + 1 / (x * y + 1))) :
  IsLeast {z | ∃ x y, 0 < x ∧ 0 < y ∧ f x y = z} 4 := by
  constructor
  · -- Show 4 is in the set
    use 1, 1
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Verify that f(1, 1) = 4
      rw [h₀ 1 1]
      norm_num
  · -- Show that 4 is the minimum in the set
    rintro z ⟨x, y, hx, hy, hz⟩
    rw [h₀ x y] at hz
    have h1 : 0 < x * y := by nlinarith
    have h2 : (x ^ 2 + y ^ 2 + 2) * (1 / (x + y) + 1 / (x * y + 1)) ≥ 4 := by
      have h3 : 0 < (x + y) * (x * y + 1) := by
        positivity
      have h4 : (x^2 + y^2 + 2) * (1 / (x + y) + 1 / (x * y + 1)) - 4 ≥ 0 := by
        have h4' : (x^2 + y^2 + 2) * (1 / (x + y) + 1 / (x * y + 1)) - 4
          = ((x^2 + y^2 + 2) * ((x * y + 1) + (x + y)) - 4 * ((x + y) * (x * y + 1))) / (( (x + y) * (x * y + 1) )) := by 
          field_simp
          <;> ring
        rw [h4']
        apply div_nonneg
        · -- Show the numerator is non-negative
          nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1),
            sq_nonneg (x * y - 1), sq_nonneg (x + y - 2), mul_pos hx hy, sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y - 2)]
        · -- Show the denominator is positive
          positivity
      linarith
    linarith