import Mathlib

open Real

theorem algebra_1876 {r : ℝ} (hr : r^2 - 80 = 2 * r + 2 * sqrt (160 - r^2)) :
    (r - 1)^4 - 162 * (r - 1)^2 + 81^2 = 640 - 4 * r^2 := by

  have h1 : r^2 - 80 - 2 * r = 2 * sqrt (160 - r^2) := by
    linarith

  have h3 : ((r^2 - 80 - 2 * r) / 2)^2 = 160 - r^2 := by
    calc
      ((r^2 - 80 - 2 * r) / 2)^2 = (sqrt (160 - r^2)) ^ 2 := by 
        have h2 : (r^2 - 80 - 2 * r) / 2 = sqrt (160 - r^2) := by
          linarith [h1]
        rw [h2]
      _ = 160 - r^2 := by 
        rw [Real.sq_sqrt]
        nlinarith [show 160 - r^2 ≥ 0 from by 
          by_contra h
          push_neg at h
          have h4 : sqrt (160 - r^2) = 0 := by
            apply Real.sqrt_eq_zero'.mpr
            nlinarith
          rw [h4] at h1
          nlinarith
        ]
  have h4 : (r^2 - 80 - 2 * r) ^ 2 = 4 * (160 - r^2) := by
    calc
      (r^2 - 80 - 2 * r) ^ 2 = (4 : ℝ) * ((r^2 - 80 - 2 * r) / 2)^2 := by 
        ring_nf
      _ = 4 * (160 - r^2) := by
        rw [h3]
        <;> ring_nf
  nlinarith [sq_nonneg (r^2 - 80 - 2 * r), sq_nonneg (r^2 - 4 * 5), sq_nonneg (r - 1), sq_nonneg (r + 1), sq_nonneg ((r -1)^2 -49), sq_nonneg (r^2 -19)]