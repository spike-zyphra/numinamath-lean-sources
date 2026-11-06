import Mathlib

theorem algebra_175854 {l w : ℝ} (hl : l > 0) (hw : w > 0)
    (h1 : (l * 0.9 + w * 0.8) / (l + w) = 0.88) :
    (l * 0.8 + w * 0.9) / (l + w) = 0.82 := by
  have h2 : l + w ≠ 0 := by
    linarith
  have eq1 : l * 0.9 + w * 0.8 = 0.88 * (l + w) := by
    have h3 : l + w ≠ 0 := h2
    field_simp at h1 ⊢
    linarith
  have h3 : l = 4 * w := by
    ring_nf at eq1 ⊢
    linarith
  have eq2 : l * 0.8 + w * 0.9 = 0.82 * (l + w) := by
    rw [h3]
    ring
  have h4 : l + w ≠ 0 := h2
  field_simp at *
  linarith [eq2]