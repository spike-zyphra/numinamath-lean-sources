import Mathlib

theorem algebra_33 (vA vB : ℝ) (h : vA > 0) (h' : vB > 0)
    (h1 : 315 / (vA + vB) = 3) (h2 : 315 / (vA - vB) = 6)
    (h3 : vA / vB = 4 / 3) :
    vA * 6 = 517.5 := by
  have eq1 : vA + vB = 105 := by
    have h1' : 315 / (vA + vB) = 3 := h1
    have pos1 : vA + vB ≠ 0 := by
      nlinarith
    field_simp at h1'
    nlinarith
  have eq2 : vA - vB = 52.5 := by
    have h2' : 315 / (vA - vB) = 6 := h2
    have pos2 : vA - vB ≠ 0 := by
      by_contra h0
      have h0' : vA = vB := by linarith
      rw [show vA / vB = (vB) / (vB) by rw [h0']] at h3
      have h4 : vB ≠ 0 := by linarith
      field_simp at h3
      <;> nlinarith
    field_simp at h2'
    nlinarith
  have h4 : vA * 3 = 4 * vB := by
    have h3' : vA / vB = 4 / 3 := h3
    have pos3 : vB ≠ 0 := by linarith
    field_simp at h3'
    nlinarith
  have eq3 : vA = 78.75 := by
    nlinarith [eq1, eq2]
  have eq4 : vB = 26.25 := by
    nlinarith [eq1, eq3]
  nlinarith [h4, eq3, eq4]