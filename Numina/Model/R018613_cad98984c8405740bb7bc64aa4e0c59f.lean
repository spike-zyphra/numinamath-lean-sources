import Mathlib

theorem algebra_194694 (d t1 t2 t3 : ℝ) (ht1 : t1 > 0) (ht2 : t2 > 0) (ht3 : t3 > 0)
    (h1 : d / t1 = d / t2 - 100) (h2 : d / t1 = d / t3 + 150) (h3 : t1 = (4 / 3) * t2)
    (h4 : t1 = t3 - 2) : d = 600 := by
  have eq1 : d * t2 = d * t1 - 100 * t1 * t2 := by
    have h1' : t1 > 0 := ht1
    have h2' : t2 > 0 := ht2
    have eq1 : d / t1 = d / t2 - 100 := h1
    field_simp [h1', h2'] at eq1 ⊢
    linarith
  have eq2 : d * t3 = d * t1 + 150 * t1 * t3 := by
    have h1' : t1 > 0 := ht1
    have h3' : t3 > 0 := ht3
    have eq2 : d / t1 = d / t3 + 150 := h2
    field_simp [h1', h3'] at eq2 ⊢
    linarith
  have eq3 : t2 = (3 / 4) * t1 := by
    linarith [h3]
  have eq4 : d = 300 * t1 := by
    rw [eq3] at eq1
    nlinarith [sq_pos_of_pos ht1]
  have eq5 : t3 = 2 * t1 := by
    rw [eq4] at eq2
    nlinarith [sq_pos_of_pos ht1]
  have eq6 : t1 = 2 := by
    nlinarith [h4, eq5]
  have eq7 : d = 600 := by
    linarith [eq4, eq6]
  linarith