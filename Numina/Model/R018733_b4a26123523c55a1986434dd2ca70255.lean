import Mathlib

theorem algebra_127872 {w l : ℝ} (hw : w > 0) (hl : l > 0)
    (h : 2 * (1.1 * w + 1.2 * l) = 1.18 * (2 * (w + l))) :
    w / l = 1 / 4 := by
  have h1 : 2 * (1.1 * w + 1.2 * l) = 1.18 * (2 * (w + l)) := h
  have h2 : l = 4 * w := by
    ring_nf at h1
    nlinarith
  have h3 : w / l = 1 / 4 := by
    have hl' : l = 4 * w := h2
    rw [hl']
    have hw' : w > 0 := hw
    field_simp
    <;> nlinarith
  exact h3