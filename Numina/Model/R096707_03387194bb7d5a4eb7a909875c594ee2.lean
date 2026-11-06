import Mathlib

theorem algebra_142757 {l w d : ℝ} (hl : l > 0) (hw : w > 0) (hd : d > 0)
    (h1 : d = 12 * l) (h2 : l = 3 / 2 * w) (h3 : d * l * w + l * w = 7 / 6) :
    d = 6 := by
  have hw_eq : w = 2 / 3 * l := by
    nlinarith
  rw [h1, hw_eq] at h3
  -- Let's compute the cubic equation
  have h4 : 48 * l ^ 3 + 4 * l ^ 2 - 7 = 0 := by
    nlinarith
  have h5 : l = 1 / 2 := by
    nlinarith [sq_nonneg (l ^ 2), sq_nonneg (l + 1 / 2), sq_nonneg (l - 1 / 2), mul_pos hl hw, mul_pos hd hw, mul_pos hd hl]
  rw [h5] at h1
  nlinarith