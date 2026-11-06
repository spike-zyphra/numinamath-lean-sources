import Mathlib

theorem algebra_289514 {l w : ℝ} (hl : l > 0) (hw : w > 0)
    (h : (l * 0.9 + w * 0.8) / (l + w) = 0.88) :
    ((l * 0.8 + w * 0.9) / (l + w)) = 0.82 := by
  have eq1 : l + w ≠ 0 := by
    positivity
  have eq2 : l * 0.9 + w * 0.8 = 0.88 * (l + w) := by
    field_simp [eq1] at h
    linarith
  have h1 : l = 4 * w := by
    ring_nf at eq2
    linarith
  have eq3 : l * 0.8 + w * 0.9 = 0.82 * (l + w) := by
    rw [show l = 4 * w by linarith [h1]]
    ring_nf
    <;> nlinarith
  field_simp [eq1]
  nlinarith [eq3]