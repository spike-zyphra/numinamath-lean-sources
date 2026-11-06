import Mathlib

theorem algebra_190818 (x : ℝ) (hx : x ^ 2 - 1 > 0) :
    x - x / Real.sqrt (x ^ 2 - 1) = 91 / 60 ↔ x = -13 / 12 ∨ x = 13 / 5 := by
  constructor
  · -- Assume x - x / Real.sqrt (x^2 - 1) = 91 / 60, prove x = -13 / 12 ∨ x = 13 / 5
    intro h_eq
    have h1 : Real.sqrt (x ^ 2 - 1) > 0 := by
      positivity

    have h_eq' : (x - x / Real.sqrt (x ^ 2 - 1)) * Real.sqrt (x ^ 2 - 1) = (91 / 60) * Real.sqrt (x ^ 2 - 1) := by
      rw [h_eq]

    have eq2 : x * Real.sqrt (x ^ 2 - 1) - x = (91 / 60) * Real.sqrt (x ^ 2 - 1) := by
      have eq3 : (x - x / Real.sqrt (x ^ 2 - 1)) * Real.sqrt (x ^ 2 - 1) = x * Real.sqrt (x ^ 2 - 1) - x := by
        field_simp [h1]
        <;> nlinarith
      rw [eq3] at h_eq'
      nlinarith

    -- Now derive the polynomial equation from eq2
    -- Replacing squaring and sqrt
    -- We know (x * sqrt (x^2-1) - x)^2 = ((91 / 60) * sqrt (x^2 - 1))^2
    -- Let's compute directly using Lean's `nlinarith`
    have h_eq : (x + 13 / 12) * (x - 13 / 5) = 0 := by
      nlinarith [Real.sqrt_nonneg (x^2 - 1), Real.sq_sqrt (show 0 ≤ x^2 - 1 by linarith)]
    
    cases' (mul_eq_zero.1 h_eq) with h6 h7
    · -- First case, where x + 13/12 = 0.
      left
      linarith
    · -- Second case, where x - 13/5 = 0.
      right
      linarith
  · -- Assume x = -13 / 12 ∨ x = 13 / 5 prove x - x / Real.sqrt (x ^ 2 - 1) = 91 / 60
    rintro (h_eq | h_eq)
    · -- Case x = -13/12
      rw [h_eq]
      have h1 : Real.sqrt ((-13 / 12 : ℝ) ^2 - 1) = 5 / 12 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      norm_num
    · -- Case x = 13/5
      rw [h_eq]
      have h1 : Real.sqrt ((13 / 5 : ℝ) ^ 2 - 1) = 12 / 5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      norm_num