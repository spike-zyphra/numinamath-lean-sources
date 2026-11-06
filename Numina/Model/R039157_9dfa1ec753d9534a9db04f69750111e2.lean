import Mathlib

theorem algebra_19905 {l w : ℝ} (hw : w ≠ 0) (h₀ : l / w = 5 / 3) (h₁ : 2 * (l + w) = 48) :
    l * w = 135 := by
  have h2 : 3 * l = 5 * w := by
    have hwne : w ≠ 0 := hw
    field_simp [hwne] at h₀
    linarith
  have h3 : l + w = 24 := by
    linarith
  have hw9 : w = 9 := by
    have h4 : 3 * l = 5 * w := h2
    have h5 : l + w = 24 := h3
    have h6 : l = 24 - w := by linarith
    rw [h6] at h4
    linarith
  have hl15 : l = 15 := by 
    linarith [hw9, h3]
  rw [hl15, hw9]
  norm_num