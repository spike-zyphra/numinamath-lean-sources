import Mathlib

theorem algebra_2119 {a b : ℝ} (ha : -1 / a = -8) (hb : 1 / (-b) = -8) : a = b := by
  have h1 : a ≠ 0 := by
    by_contra h
    rw [h] at ha
    norm_num at ha
  have h2 : b ≠ 0 := by
    by_contra h
    rw [h] at hb
    norm_num at hb
  have ha' : 1 / a = 8 := by 
    have h : -1 / a = -8 := ha
    field_simp [h1] at h ⊢
    nlinarith
  have hb' : 1 / b = 8 := by
    have h : 1 / (-b) = -8 := hb
    have h3 : -b ≠ 0 := by
      intro h4
      apply h2
      linarith
    have : 1 / b = 8 := by
      field_simp [h3] at h ⊢
      nlinarith
    assumption
  have ha'' : a = 1 / 8 := by
    field_simp [h1] at ha' ⊢
    linarith
  have hb'' : b = 1 / 8 := by
    field_simp [h2] at hb' ⊢
    linarith
  linarith [ha'', hb'']