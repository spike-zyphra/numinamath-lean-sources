import Mathlib

theorem algebra_159791 {x y : ℝ} (h1 : 2*x+Real.sqrt (2*x+3*y)-3*y=5) (h2 : 4*x^2+2*x+3*y-9*y^2=32) :
    x=17/4 ∧ y=5/2 := by

  have h3 : 2 * x + 3 * y ≥ 0 := by
    by_contra h
    push_neg at h

    have h4 : Real.sqrt (2 * x + 3 * y) = 0 := by
      rw [Real.sqrt_eq_zero']
      nlinarith
      all_goals nlinarith

    have h5 : 2 * x - 3 * y = 5 := by 
      nlinarith [h1, h4]

    have h6 : x = (5 + 3 * y) / 2 := by 
      linarith [h5]

    rw [show x = (5 + 3 * y) / 2 by linarith [h6] ] at h2

    nlinarith

  have h4 : Real.sqrt (2 * x + 3 * y) ≥ 0 := by
    apply Real.sqrt_nonneg

  have ht2 : (Real.sqrt (2 * x + 3 * y)) ^ 2 = 2 * x + 3 * y := by
    exact Real.sq_sqrt (show 0 ≤ (2 * x + 3 * y : ℝ) by linarith [h3] )

  have eq1 : 2 * x + Real.sqrt (2 * x + 3 * y) - 3 * y = 5 := by 
    linarith [h1]

  have eq2 : Real.sqrt (2 * x + 3 * y) = 5 - (2 * x - 3 * y) := by 
    nlinarith [eq1]

  rw [eq2] at ht2

  have h5 : (x - 17 / 4) ^ 2 + (y - 5 / 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 17 / 4), sq_nonneg (y - 5 / 2), sq_nonneg (5 - (2 * x - 3 * y) - (5 / 2)), Real.sqrt_nonneg (2 * x + 3 * y), h3, h2]

  have hx1 : x - 17 / 4 = 0 := by
    nlinarith [h5, sq_nonneg (x - 17 / 4), sq_nonneg (y - 5 / 2)]

  have hy1 : y - 5 / 2 = 0 := by
    nlinarith [h5, sq_nonneg (x - 17 / 4), sq_nonneg (y - 5 / 2)]

  constructor
  · linarith [hx1]
  · linarith [hy1]