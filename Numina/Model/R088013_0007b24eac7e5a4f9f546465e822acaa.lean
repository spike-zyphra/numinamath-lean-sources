import Mathlib

theorem algebra_103134 {x y z : ℚ} (hx : x ≠ -1) (hy : y ≠ -2) (hz : z ≠ -3)
    (h : 2015 / (x + 1) + 2015 / (y + 2) + 2015 / (z + 3) = 2014) :
    (x - 1) / (x + 1) + y / (y + 2) + (z + 1) / (z + 3) = 2017 / 2015 := by

  have h1 : x + 1 ≠ 0 := by
    intro h2
    apply hx
    linarith

  have h2 : y + 2 ≠ 0 := by
    intro h3
    apply hy
    linarith

  have h3 : z + 3 ≠ 0 := by
    intro h4
    apply hz
    linarith

  have h4 : 1 / (x + 1) + 1 / (y + 2) + 1 / (z + 3) = 2014 / 2015 := by
    have h_eq : 2015 / (x + 1) + 2015 / (y + 2) + 2015 / (z + 3) = 2014 := by
      linarith
    field_simp [h1, h2, h3] at h_eq ⊢
    linarith

  have eq : (x - 1) / (x + 1) + y / (y + 2) + (z + 1) / (z + 3) = 3 - 2 * (1 / (x + 1) + 1 / (y + 2) + 1 / (z + 3)) := by
    have hx1 : x + 1 ≠ 0 := h1
    have hy2 : y + 2 ≠ 0 := h2
    have hz3 : z + 3 ≠ 0 := h3
    field_simp [hx1, hy2, hz3]
    <;> ring

  rw [eq]
  rw [h4]
  norm_num