import Mathlib

theorem algebra_5600 (x : ℝ) : x^3 + 4*x^2 + 5*x + 2 = 0 ↔ x = -1 ∨ x = -2 := by
  constructor
  · -- Assume the equation, prove the disjunction
    intro h
    have h1 : x^3 + 4*x^2 + 5*x + 2 = (x + 1)^2 * (x + 2) := by
      ring
    rw [h1] at h
    cases' (mul_eq_zero.mp h) with h2 h3
    · -- Case where $(x + 1)^2 = 0$
      have h4 : x + 1 = 0 := by
        apply pow_eq_zero
        exact h2
      have hx1 : x = -1 := by
        linarith
      left
      exact hx1
    · -- Case where $(x + 2) = 0$
      have hx2 : x = -2 := by
        linarith
      right
      exact hx2
  · -- Assume the disjunction, prove the equation
    rintro (h | h)
    · -- Case x = -1
      rw [h]
      norm_num
    · -- Case x = -2
      rw [h]
      norm_num