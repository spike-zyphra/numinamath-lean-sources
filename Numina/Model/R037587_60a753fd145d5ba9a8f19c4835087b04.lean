import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_22580 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ x, a * Real.sin (b * x + c) = 2 * Real.sin (4 * x + Real.pi / 2)) :
    a = 2 := by
  have eq1 := h 0
  have eq14 := h (Real.pi / (2 * b) - c / b)
  have eq3 : a * Real.sin (b * (Real.pi / (2 * b) - c / b) + c) = 2 * Real.sin (4 * (Real.pi / (2 * b) - c / b) + Real.pi / 2) := by
    apply h
  have eq4 : b * (Real.pi / (2 * b) - c / b) + c = Real.pi / 2 := by
    field_simp [hb.ne']
    <;> ring
  have eq5 : a * Real.sin (b * (Real.pi / (2 * b) - c / b) + c) = a * 1 := by
    rw [eq4]
    have h30 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    rw [h30]
  have eq5a : a * 1 = 2 * Real.sin (4 * (Real.pi / (2 * b) - c / b) + Real.pi / 2) := by
    nlinarith [eq5, eq3]
  have h2a : a ≤ 2 := by
    have h17 : -1 ≤ Real.sin (4 * (Real.pi / (2 * b) - c / b) + Real.pi / 2) ∧ Real.sin (4 * (Real.pi / (2 * b) - c / b) + Real.pi / 2) ≤ 1 := by
      constructor
      · apply Real.neg_one_le_sin
      · apply Real.sin_le_one
    nlinarith [eq5a, h17.right]
  have h3 : a * Real.sin (b * (0 : ℝ) + c) = 2 := by
    simpa using eq1
  have h4 : a * Real.sin (b * (0 : ℝ) + c) ≤ a * 1 := by
    have h5 : Real.sin (b * (0 : ℝ) + c) ≤ 1 := by
      apply Real.sin_le_one
    have h11 : a ≥ 0 := by linarith
    nlinarith [h5, h11]
  have h8 : Real.sin (b * (0 : ℝ) + c) = 1 := by
    nlinarith [h3, h4, ha]
  nlinarith [h2a, h3, h8, ha]