import Mathlib

theorem algebra_93916 (x : ℝ) (hx : x ≠ -1 ∧ x ≠ 1) :
    ((x + 1)^2 * (x^2 - x + 1)^2 / (x^3 + 1)^2)^2 *
    ((x - 1)^2 * (x^2 + x + 1)^2 / (x^3 - 1)^2)^2 = 1 := by

  have h1 : x ≠ -1 := hx.1
  have h2 : x ≠ 1 := hx.2
  have h3 : x + 1 ≠ 0 := by
    intro h
    apply h1
    linarith
  have h4 : x - 1 ≠ 0 := by
    intro h
    apply h2
    linarith
  have h5 : x^3 + 1 = (x + 1) * (x^2 - x + 1) := by
    ring
  have h6 : x^3 - 1 = (x - 1) * (x^2 + x + 1) := by
    ring

  have h7 : (x^3 + 1)^2 = (x + 1)^2 * (x^2 - x + 1)^2 := by
    rw [h5]
    ring
  have h8 : (x^3 - 1)^2 = (x - 1)^2 * (x^2 + x + 1)^2 := by
    rw [h6]
    ring
  have h9 : (x^3 + 1)^2 ≠ 0 := by
    have h10 : (x + 1) ≠ 0 := h3
    have h11 : (x^2 - x + 1) ≠ 0 := by
      nlinarith [sq_nonneg (x - 1/2)]
    have h13 : (x + 1)^2 ≠ 0 := by
      apply pow_ne_zero 2
      exact h10
    have h14 : (x^2 - x + 1)^2 ≠ 0 := by
      apply pow_ne_zero 2
      exact h11
    rw [h7]
    exact mul_ne_zero h13 h14
  have h15 : (x^3 - 1)^2 ≠ 0 := by
    have h16 : (x - 1) ≠ 0 := h4
    have h17 : (x^2 + x + 1) ≠ 0 := by
      nlinarith [sq_nonneg (x + 1/2)]
    have h18 : (x - 1)^2 ≠ 0 := by
      apply pow_ne_zero 2
      exact h16
    have h19 : (x^2 + x + 1)^2 ≠ 0 := by
      apply pow_ne_zero 2
      exact h17
    rw [h8]
    exact mul_ne_zero h18 h19
  have h10 : ((x + 1)^2 * (x^2 - x + 1)^2 / (x^3 + 1)^2) = 1 := by
    rw [h7]
    field_simp [show (x + 1) ≠ 0 by exact h3, show (x^2 - x + 1) ≠ 0 by nlinarith [sq_nonneg (x - 1/2)]]
    <;> nlinarith
  have h11 : ((x - 1)^2 * (x^2 + x + 1)^2 / (x^3 - 1)^2) = 1 := by
    rw [h8]
    field_simp [show (x - 1) ≠ 0 by exact h4, show (x^2 + x + 1) ≠ 0 by nlinarith [sq_nonneg (x + 1/2)]]
    <;> nlinarith
  rw [h10, h11]
  norm_num