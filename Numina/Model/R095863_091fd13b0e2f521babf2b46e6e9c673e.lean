import Mathlib

theorem algebra_305472 (l w h k : ℝ) (hl : l > 0) (hw : w > 0) (hw' : h > 0)
    (hvol : l * w * h = 1) (hsum : l + w + h = k) (hsurf : 2 * (l * w + w * h + l * h) = 2 * k) :
    k ≥ 3 := by
  have h1 : l * w * h = 1 := hvol
  have h2 : k = l + w + h := by linarith
  have h3 : l + w + h ≥ 3 := by
    nlinarith [sq_nonneg (l - 1), sq_nonneg (w - 1), sq_nonneg (h - 1),
      mul_pos hl hw, mul_pos hw hw', mul_pos hl hw']
  linarith