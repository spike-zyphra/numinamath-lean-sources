import Mathlib

theorem algebra_215625 (d v : ℝ) (h : d > 0) (h1 : v > 0) (h2 : d / v = 12) (h3 : v + 16 = d / (6 * v)) (h4 : d - 80 = 6 * v) :
    d = 280 := by
  have eq1 : 6 * v = d - 80 := by
    linarith
  have eq3 : d = 12 * v := by
    have pos1 : v ≠ 0 := by
      linarith
    field_simp at h2 ⊢
    nlinarith
  have eq5 : v = 40 / 3 := by
    have eq6 : d = 12 * v := eq3
    rw [eq6] at eq1
    nlinarith
  have eq7 : d = 160 := by
    rw [eq5] at eq3
    nlinarith
  have eq8 : d / (6 * v) = 2 := by
    rw [eq7, eq5]
    norm_num
  have eq9 : v + 16 = d / (6 * v) := h3
  rw [eq8] at eq9
  rw [eq5] at eq9
  nlinarith