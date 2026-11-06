import Mathlib

theorem inequalities_308498 (a : ℝ) (h : ∀ x, (3 * x - 3 ≥ 6 * x + a ∧ x ≥ 1) ↔ (1 ≤ x ∧ x ≤ 3)) :
    a = -12 := by
  have h1 := h 3
  norm_num at h1
  have h2 : a ≤ -12 := by
    linarith
  have h5 : a ≥ -12 := by
    by_contra h5
    push_neg at h5
    have h6 := h ((-a - 3 : ℝ) / 3)
    have h7 : (-a - 3 : ℝ) / 3 ≥ 1 := by
      nlinarith
    have h8 : 3 * ((-a - 3 : ℝ) / 3) - 3 ≥ 6 * ((-a - 3 : ℝ) / 3) + a := by
      nlinarith
    have h9 : 1 ≤ ((-a - 3 : ℝ) / 3) := by
      nlinarith
    have h10 : (1 ≤ ((-a - 3 : ℝ) / 3) ∧ ((-a - 3 : ℝ) / 3) ≤ 3) := by
      tauto
    have h11 : ((-a - 3 : ℝ) / 3) ≤ (3 : ℝ) := by
      linarith [h10]
    nlinarith
  linarith