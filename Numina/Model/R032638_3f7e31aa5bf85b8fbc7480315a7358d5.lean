import Mathlib

theorem algebra_2129 (x : ℝ) :
    x^4 + x^3 - 16 * x^2 - 4 * x + 48 = 0 ↔ x = -4 ∨ x = -2 ∨ x = 2 ∨ x = 3 := by
  constructor
  · -- Forward implication: if the equation holds, prove the disjunction
    intro h
    have h1 : x^4 + x^3 - 16 * x^2 - 4 * x + 48 = (x + 4) * (x + 2) * (x - 2) * (x - 3) := by
      ring
    rw [h1] at h
    cases' (mul_eq_zero.mp h) with h2 h3
    · -- Case where (x + 4) * (x + 2) * (x - 2) = 0
      cases' (mul_eq_zero.mp h2) with h4 h5
      · -- Case where (x + 4) * (x + 2) = 0
        cases' (mul_eq_zero.mp h4) with h6 h7
        · -- Case where x + 4 = 0, so x = -4
          have hx4 : x = -4 := by linarith
          left
          exact hx4
        · -- Case where x + 2 = 0, so x = -2
          have hx2 : x = -2 := by linarith
          right
          left
          exact hx2
      · -- Case where x - 2 = 0, so x = 2
        have hx2 : x = 2 := by linarith
        right
        right
        left
        exact hx2
    · -- Case where x - 3 = 0, so x = 3
      have hx3 : x = 3 := by linarith
      right
      right
      right
      exact hx3
  · -- Backward implication: if one of the disjunctions holds, prove the equation
    rintro (h | h | h | h)
    · -- Case x = -4
      rw [h]
      norm_num
    · -- Case x = -2
      rw [h]
      norm_num
    · -- Case x = 2
      rw [h]
      norm_num
    · -- Case x = 3
      rw [h]
      norm_num