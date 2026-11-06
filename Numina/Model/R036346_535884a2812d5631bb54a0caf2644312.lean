import Mathlib

theorem algebra_199008 (x : ℝ) (hx : x ≠ -2) : x^2 + 4 * x^2 / (x + 2)^2 = 5 ↔ x = -1 ∨ x = 2 := by
  constructor
  · -- Assume the equation holds, prove x = -1 or x = 2
    intro h
    have h1 : x + 2 ≠ 0 := by
      intro h2
      apply hx
      linarith
    have eq1 : x^2 + 4 * x^2 / (x + 2) ^2 = 5 := by linarith [h]
    have eq2 : x^2 * (x + 2) ^ 2 + 4 * x^2 = 5 * (x + 2) ^ 2 := by 
      have h1' : (x + 2) ≠ 0 := h1
      field_simp [h1'] at eq1 ⊢
      nlinarith [eq1]
    have eq3 : x ^ 4 + 4 * x ^ 3 + 3 * x ^ 2 - 20 * x - 20 = 0 := by
      nlinarith [eq2]
    have eq4 : (x + 1) * (x - 2) * (x ^ 2 + 5 * x + 10) = 0 := by
      nlinarith [eq3]
    cases' (mul_eq_zero.mp eq4) with eq5 eq6
    cases' (mul_eq_zero.mp eq5) with eq7 eq8
    · -- Case x + 1 = 0
      left
      linarith
    · -- Case x - 2 = 0
      right
      linarith
    · -- Case x^2 + 5 * x + 10 = 0
      have h2 : x ^ 2 + 5 * x + 10 > 0 := by
        nlinarith [sq_nonneg (x + 5 / 2)]
      have h3 : x ^ 2 + 5 * x + 10 = 0 := by
        nlinarith [eq6]
      nlinarith [h2, h3]
  · -- Verify that x = -1 and x = 2 satisfy the equation
    rintro (h | h)
    · -- Substitute x = -1 into the equation
      rw [h]
      norm_num
    · -- Substitute x = 2 into the equation
      rw [h]
      norm_num