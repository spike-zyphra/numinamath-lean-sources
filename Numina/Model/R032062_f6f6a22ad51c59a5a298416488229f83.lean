import Mathlib
theorem algebra_122581 (x : ℝ) :
    (x^2 + x - 2)^3 + (2 * x^2 - x - 1)^3 = 27 * (x^2 - 1)^3 ↔
    x = 1 ∨ x = -1 ∨ x = -2 ∨ x = -1 / 2 := by
  constructor
  · -- Assume the equation holds, prove the roots
    intro h_eq
    have h_eq1 : (x^2 + x - 2)^3 + (2 * x^2 - x - 1)^3 - 27 * (x^2 - 1)^3 = 0 := by linarith
    have h_eq2 : (x - 1)^3 * (x + 1) * (x + 2) * (2 * x + 1) = 0 := by
      ring_nf at h_eq1 ⊢
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 2), sq_nonneg (2 * x + 1), sq_nonneg ((x - 1) * (x + 1)), sq_nonneg ((x - 1) * (x + 2)), sq_nonneg ((x - 1) * (2 * x + 1)), sq_nonneg ((x + 1) * (x + 2)), sq_nonneg ((x + 1) * (2 * x + 1)), sq_nonneg ((x + 2) * (2 * x + 1)), sq_nonneg ((x - 1)^2 * (x + 1)), sq_nonneg ((x - 1)^2 * (x + 2)), sq_nonneg ((x - 1)^2 * (2 * x + 1))]
    cases' (mul_eq_zero.mp h_eq2) with h_eq3 h_eq4
    cases' (mul_eq_zero.mp h_eq3) with h_eq5 h_eq6
    cases' (mul_eq_zero.mp h_eq5) with h_eq7 h_eq8
    · -- Case (x - 1)^3 = 0 so x = 1
      have h_eq9 : x - 1 = 0 := by
        have h1 : (x - 1) ^ 3 = 0 := by
          nlinarith
        have h2 : x - 1 = 0 := by
          have h3 : (x - 1) ^ 3 = 0 := h1
          simp at h3 ⊢
          <;> nlinarith
        linarith
      left
      linarith
    · -- Case x + 1 = 0 so x = -1
      have h_eq10 : x + 1 = 0 := by
        nlinarith
      right
      left
      linarith
    · -- Case x + 2 = 0 so x = -2
      have h_eq11 : x + 2 = 0 := by
        nlinarith
      right
      right
      left
      linarith
    · -- Case 2 * x + 1 = 0 so x = -1 / 2
      have h_eq12 : 2 * x + 1 = 0 := by
        nlinarith
      right
      right
      right
      linarith
  · -- Assume the roots, prove the equation
    rintro (h | h | h | h)
    · -- Case x = 1
      rw [h]
      norm_num
    · -- Case x = -1
      rw [h]
      norm_num
    · -- Case x = -2
      rw [h]
      norm_num
    · -- Case x = -1/2
      rw [h]
      norm_num