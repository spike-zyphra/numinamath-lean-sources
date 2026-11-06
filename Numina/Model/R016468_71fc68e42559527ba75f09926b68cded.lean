import Mathlib

theorem algebra_237463 {a b c : ℝ} (ha : a ≠ 0) (h : 5 * a + 3 * b + 2 * c = 0) :
    ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ a * x1 ^ 2 + b * x1 + c = 0 ∧ a * x2 ^ 2 + b * x2 + c = 0 := by

  have h1 : c = (-5 * a - 3 * b) / 2 := by
    linarith

  have h2 : b ^ 2 + 10 * a ^ 2 + 6 * a * b > 0 := by
    have h3 : b ^ 2 + 10 * a ^ 2 + 6 * a * b = (b + 3 * a) ^ 2 + a ^ 2 := by
      ring
    rw [h3]
    have h4 : a ^ 2 > 0 := by
      exact sq_pos_of_ne_zero ha
    have h5 : (b + 3 * a) ^ 2 ≥ 0 := by
      apply sq_nonneg
    linarith

  use (-b + Real.sqrt (b ^ 2 + 10 * a ^ 2 + 6 * a * b)) / (2 * a), 
      (-b - Real.sqrt (b ^ 2 + 10 * a ^ 2 + 6 * a * b)) / (2 * a)
  constructor
  · -- Show x1 ≠ x2
    by_contra h_eq
    have h_eq1 : (-b + Real.sqrt (b ^ 2 + 10 * a ^ 2 + 6 * a * b)) / (2 * a) = (-b - Real.sqrt (b ^ 2 + 10 * a ^ 2 + 6 * a * b)) / (2 * a) := by 
      linarith [h_eq]
    have h_eq2 : (-b + Real.sqrt (b ^ 2 + 10 * a ^ 2 + 6 * a * b)) = (-b - Real.sqrt (b ^ 2 + 10 * a ^ 2 + 6 * a * b)) := by 
      field_simp [ha] at h_eq1 ⊢
      all_goals nlinarith
    have h_eq3 : Real.sqrt (b ^ 2 + 10 * a ^ 2 + 6 * a * b) = 0 := by
      nlinarith [h_eq2, Real.sqrt_nonneg (b ^ 2 + 10 * a ^ 2 + 6 * a * b)]
    have h_eq4 : b ^ 2 + 10 * a ^ 2 + 6 * a * b = 0 := by 
      rw [Real.sqrt_eq_zero (by nlinarith)] at h_eq3 
      linarith
    linarith [h_eq4, h2]

  constructor
  · -- Show that the first root is a solution 
    have h_eq5 : c = (-5 * a - 3 * b) / 2 := h1
    rw [h_eq5]
    field_simp [ha]
    <;> nlinarith [Real.sqrt_pos.mpr (show b ^ 2 + 10 * a ^ 2 + 6 * a * b > 0 by linarith [h2]), 
                  Real.sq_sqrt (show b ^ 2 + 10 * a ^ 2 + 6 * a * b ≥ 0 by nlinarith [h2]), sq_pos_of_ne_zero ha]

  · -- Show that the second root is a solution 
    have h_eq5 : c = (-5 * a - 3 * b) / 2 := h1
    rw [h_eq5]
    field_simp [ha]
    <;> nlinarith [Real.sqrt_pos.mpr (show b ^ 2 + 10 * a ^ 2 + 6 * a * b > 0 by linarith [h2]), 
                  Real.sq_sqrt (show b ^ 2 + 10 * a ^ 2 + 6 * a * b ≥ 0 by nlinarith [h2]), sq_pos_of_ne_zero ha]