import Mathlib

theorem algebra_220882 {x : ℝ} (hx : x ≠ 0) (h : x + Real.sqrt (x^2 - x) = 2) :
    x = 4 / 3 := by
  have h1 : Real.sqrt (x^2 - x) = 2 - x := by linarith [h]

  have h2 : 2 - x ≥ 0 := by
    have h3 : Real.sqrt (x^2 - x) ≥ 0 := by positivity
    linarith [h1, h3]

  have h4 : x ^ 2 - x ≥ 0 := by
    by_contra h5
    push_neg at h5
    have h6 : Real.sqrt (x ^ 2 - x) = 0 := by
      rw [Real.sqrt_eq_zero']
      linarith
      all_goals nlinarith
    rw [h6] at h1
    have h7 : x = 2 := by linarith
    rw [h7] at h5
    nlinarith

  have h5 : (Real.sqrt (x^2 - x)) ^ 2 = (2 - x) ^ 2 := by
    rw [h1]

  have h6 : (Real.sqrt (x^2 - x)) ^ 2 = x^2 - x := Real.sq_sqrt (by linarith)

  rw [h6] at h5

  have h7 : x^2 - x = 4 - 4*x + x^2 := by
    nlinarith [h5]

  have h8 : x = 4 / 3 := by
    nlinarith

  linarith [h8]