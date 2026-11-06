import Mathlib

theorem algebra_141825 {a b : ℝ} (ha : a < 0) (hb : b < 0)
    (h : (a * b + a) * (a * b + b) = -9) : a + b < -6 := by 
  by_contra h1
  push_neg at h1 
  have h2 : a * b > 0 := by nlinarith
  have h3 : a + b < 0 := by linarith 
  have h4 : a * b * (a + 1) * (b + 1) = -9 := by
    nlinarith 
  have h5 : (a + b + 1) ^ 2 ≥ 36 := by 
    nlinarith [sq_nonneg (a * b - 4), sq_nonneg (a - b), sq_nonneg (a + b + 6), 
        sq_nonneg (a * (b + 1)), sq_nonneg (b * (a + 1)), 
          mul_pos (show 0 < (-a) by linarith) (show 0 < (-b) by linarith), 
            mul_pos (show 0 < a * b by linarith) (show 0 < (-a) * (-b) by nlinarith)
      ]
  nlinarith