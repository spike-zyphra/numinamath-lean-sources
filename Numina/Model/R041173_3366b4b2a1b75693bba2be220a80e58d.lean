import Mathlib

theorem algebra_144738 {x y : ℝ} (hx : 2*x+Real.sqrt (2*x+3*y)-3*y=5) (hy : 4*x^2+2*x+3*y-9*y^2=32) :
    (x,y)=(17/4,5/2) := by
  have h1 : 2 * x + 3 * y ≥ 0 := by
    by_contra h
    push_neg at h
    have h2 : Real.sqrt (2 * x + 3 * y) = 0 := by
      rw [Real.sqrt_eq_zero'.mpr]
      nlinarith
    rw [h2] at hx
    nlinarith
  have h2 : Real.sqrt (2 * x + 3 * y) = 4 := by
    nlinarith [sq_nonneg (Real.sqrt (2 * x + 3 * y) - 4), 
          Real.sqrt_nonneg (2 * x + 3 * y), 
          sq_nonneg (x - 17 / 4), sq_nonneg (y - 5 / 2), 
          Real.sq_sqrt (show 2 * x + 3 * y ≥ 0 by linarith)]
  have h3 : 2 * x + 3 * y = 16 := by
    calc
      2 * x + 3 * y = (Real.sqrt (2 * x + 3 * y)) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      _ = (4) ^ 2 := by
        rw [h2]
      _ = (16 : ℝ) := by norm_num
  have hx1 : x = 17 / 4 := by
    nlinarith [h3, h2, sq_nonneg (x - 17 / 4), sq_nonneg (y - 5 / 2)]
  have hy1 : y = 5 / 2 := by
    nlinarith [h3, h2, sq_nonneg (x - 17 / 4), sq_nonneg (y - 5 / 2), hx1]
  simp [hx1, hy1]