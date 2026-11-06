import Mathlib

theorem algebra_246674 {x y z : ℝ} (h : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0) (h1 : 4*x-3*y-6*z=0) (h2 : 6*x+5*y-28*z=0) :
    (21*x+24*y-15*z)/(3*x+4*y+7*z) = 4 := by
  have h3 : x = 3 * z := by
    linarith [h1, h2]
  have h4 : y = 2 * z := by
    rw [h3] at h1
    linarith
  have h5 : 21 * x + 24 * y - 15 * z = 4 * (3 * x + 4 * y + 7 * z) := by
    rw [h3, h4]
    linarith
  have h6 : 3 * x + 4 * y + 7 * z ≠ 0 := by
    have h7 : z ≠ 0 := h.2.2
    have h8 : 3 * x + 4 * y + 7 * z = 24 * z := by
      rw [h3, h4]
      linarith
    rw [h8]
    intro h9
    have : z = 0 := by
      linarith
    contradiction
  field_simp [h6]
  linarith [h5]