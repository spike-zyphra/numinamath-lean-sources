import Mathlib

theorem algebra_243119 (a b x : ℝ) (ha : 0 < a * b) (hx : x = Real.sqrt (a * b)) :
    ∃ r, x = a * r ∧ x = b / r := by
  use (x / a)
  have ha1 : a ≠ 0 := by
    by_contra h
    have : a * b = 0 := by
      rw [h]
      norm_num
    linarith
  have hb1 : b ≠ 0 := by
    by_contra h
    have : a * b = 0 := by
      rw [h]
      norm_num
    linarith
  have hx2 : x ^ 2 = a * b := by
    rw [hx]
    have : (Real.sqrt (a * b)) ^ 2 = a * b := Real.sq_sqrt (by nlinarith)
    linarith
  have hne : x ≠ 0 := by
    by_contra h
    have hx0 : x = 0 := by linarith
    rw [hx0] at hx2
    have : a * b = 0 := by nlinarith
    linarith
  constructor
  · -- Show x = a * r
    field_simp [ha1, hne]
  · -- Show x = b / r
    field_simp [ha1, hne]
    nlinarith [hx2]