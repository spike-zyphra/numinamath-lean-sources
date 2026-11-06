import Mathlib

theorem algebra_234308 (x : ℝ) (hx : x^3 - 2 * x^2 + 1 ≠ 0 ∧ x^3 - 3 * x^2 + 2 ≠ 0) :
    (2 * x - 1)^2 / (x^3 - 2 * x^2 + 1) + (4 * x - 4 * x^2 - 1) / (x^3 - 3 * x^2 + 2) = 0 ↔
    x = 1 / 2 ∨ x = -1 := by
  constructor
  · -- Forward implication: if the equation equals zero, prove x is 1/2 or -1
    intro h
    have hx1 : x^3 - 2 * x^2 + 1 ≠ 0 := hx.1
    have hx2 : x^3 - 3 * x^2 + 2 ≠ 0 := hx.2
    have h1 : (2 * x - 1) ^ 2 / (x^3 - 2 * x^2 + 1) + (4 * x - 4 * x^2 - 1) / (x^3 - 3 * x^2 + 2) = 0 := h
    have h2 : (2 * x - 1) ^ 2 * (x^3 - 3 * x^2 + 2) + (4 * x - 4 * x^2 - 1) * (x^3 - 2 * x^2 + 1) = 0 := by
      have hx1' : x^3 - 2 * x^2 + 1 ≠ 0 := hx1
      have hx2' : x^3 - 3 * x^2 + 2 ≠ 0 := hx2
      field_simp [hx1', hx2'] at h1 ⊢
      nlinarith
    have h3 : 4 * x^3 - 3 * x + 1 = 0 := by
      nlinarith [sq_pos_of_ne_zero (show x^3 - 2 * x^2 + 1 ≠ 0 by tauto), sq_pos_of_ne_zero (show x^3 - 3 * x^2 + 2 ≠ 0 by tauto), sq_nonneg (x^2 - x - 1), sq_nonneg (x^2 - 2 * x - 2), sq_nonneg (x * (x - 1)), sq_nonneg ((x - 1) * (x - 1))]
    have h5 : (x + 1) * (2 * x - 1) ^ 2 = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- h6 : x + 1 = 0
      right
      linarith
    · -- h7 : (2 * x - 1) ^ 2 = 0
      left
      nlinarith
  · -- Backward direction: x is 1/2 or -1, prove the equation equals zero
    rintro (h | h)
    · -- case x = 1/2
      rw [h]
      norm_num
    · -- case x = -1
      rw [h]
      norm_num