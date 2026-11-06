import Mathlib

theorem algebra_1189 (d1 d2 t1 t2 : ℝ) (h1 : d1/t1 = 120) (h2 : d2/t2 = 60)
    (h3 : t1+t2 = 6) (h4 : d1 = 6*d2) : d1+d2=630 := by
  have ht1_ne_zero : t1 ≠ 0 := by
    by_contra h
    rw [h] at h1
    norm_num at h1

  have ht2_ne_zero : t2 ≠ 0 := by
    by_contra h
    rw [h] at h2
    norm_num at h2
  
  have eq1 : d1 = 120 * t1 := by
    have : t1 ≠ 0 := ht1_ne_zero
    field_simp at h1
    linarith

  have eq2 : d2 = 60 * t2 := by
    have : t2 ≠ 0 := ht2_ne_zero
    field_simp at h2
    linarith
  
  have eq3 : t1 = 3 * t2 := by
    rw [eq1, eq2] at h4
    linarith
  
  have ht2_val : t2 = 3 / 2 := by
    linarith [h3, eq3]

  have ht1_val : t1 = 9 / 2 := by
    rw [ht2_val] at eq3
    linarith
  
  have hd1_val : d1 = 540 := by
    rw [ht1_val] at eq1
    linarith

  have hd2_val : d2 = 90 := by
    rw [ht2_val] at eq2
    linarith
  
  linarith [hd1_val, hd2_val]