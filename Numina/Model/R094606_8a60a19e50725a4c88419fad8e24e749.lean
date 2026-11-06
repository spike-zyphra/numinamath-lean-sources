import Mathlib

theorem algebra_156027 (vA vB : ℝ) (h : vA = 2 * vB) (dA dB : ℝ)
    (h1 : dA / dB = 3) (h2 : dB / dA = 7) :
    dA / dB = 5 := by
  have h3 : dB ≠ 0 := by
    by_contra h4
    rw [h4] at h1
    norm_num at h1
  have h4 : dA ≠ 0 := by
    by_contra h5
    rw [h5] at h2
    norm_num at h2
  have h3' : dA = 3 * dB := by
    have h4 : dB ≠ 0 := h3
    field_simp at h1 ⊢
    linarith
  have h4' : dB = 7 * dA := by
    have h5 : dA ≠ 0 := h4
    field_simp at h2 ⊢
    linarith
  have h5 : dA = 0 := by
    linarith [h3', h4']
  contradiction