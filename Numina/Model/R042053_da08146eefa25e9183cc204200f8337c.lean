import Mathlib

theorem algebra_206548 {x y z : ℝ} (h1 : x - y ≥ z) (h2 : x^2 + 4 * y^2 + 5 = 4 * z) :
    x = 2 ∧ y = -0.5 ∧ z = 2.5 := by
  have h3 : z = (x^2 + 4 * y^2 + 5) / 4 := by
    linarith
  have h4 : 4 * (x - y) ≥ x^2 + 4 * y^2 + 5 := by
    have h5 : x - y ≥ z := h1
    rw [h3] at h5
    nlinarith
  have h5 : (x - 2)^2 + 4 * (y + 0.5)^2 = 0 := by
    ring_nf at h4 ⊢
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 0.5), sq_nonneg (x - 2 * y)]
  have hx1 : x - 2 = 0 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 0.5)]
  have hy1 : y + 0.5 = 0 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 0.5)]
  have hx2 : x = (2 : ℝ) := by
    linarith [hx1]
  have hy2 : y = (-0.5 : ℝ) := by
    nlinarith [hy1]
  have h6 : z = (2.5 : ℝ) := by
    rw [h3]
    rw [hx2, hy2]
    norm_num
  constructor
  · -- Show x = 2
    linarith [hx2]
  constructor
  · -- Show y = -0.5
    linarith [hy2]
  · -- Show z = 2.5
    linarith [h6]