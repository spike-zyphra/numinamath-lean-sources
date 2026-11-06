import Mathlib

theorem algebra_10770 (z : ℝ) (h : Real.sqrt (2 - 3 * z) = 9) :
    z = -79 / 3 := by
  have h1 : 2 - 3 * z ≥ 0 := by 
    by_contra h2
    push_neg at h2
    have h2' : 2 - 3 * z ≤ 0 := by linarith
    have h3 : Real.sqrt (2 - 3 * z) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr h2']
      all_goals linarith
    rw [h3] at h
    all_goals nlinarith
  have h2 : (Real.sqrt (2 - 3 * z)) ^ 2 = 9 ^ 2 := by
    rw [h]
  have h3 : (Real.sqrt (2 - 3 * z)) ^ 2 = 2 - 3 * z := by
    apply Real.sq_sqrt
    linarith
  rw [h3] at h2
  nlinarith
  all_goals linarith