import Mathlib

theorem algebra_119947 (l v : ℝ) (hl : l > 0) (hv : v > 0)
    (h1 : l / (v + w) = 140) (h2 : l / (v - w) = 20) (hw : w > 0)
    (h3 : w * 140 = l) (h4 : w * 20 = l - 140) :
    l = 35 := by 
  have eq1 : w * 140 = l := h3
  have eq2 : w * 20 = l - 140 := h4

  have eq3 : w = 7 / 6 := by
    nlinarith

  have eq4 : l = 490 / 3 := by
    rw [eq3] at eq1
    linarith

  have h12 : v + w > 0 := by nlinarith
  have h11 : l / (v + w) = 140 := h1
  have h5 : l = 140 * (v + w) := by
    have h12 : v + w ≠ 0 := by nlinarith
    field_simp [h12] at h11 ⊢
    linarith
  have eq6 : v = 0 := by
    rw [eq4] at h5
    nlinarith
  linarith