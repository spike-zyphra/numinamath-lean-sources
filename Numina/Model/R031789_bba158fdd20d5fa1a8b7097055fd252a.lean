import Mathlib

open Real

theorem algebra_245482 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    x * (2 * y - z) / (1 + x + 3 * y) + y * (2 * z - x) / (1 + y + 3 * z) +
    z * (2 * x - y) / (1 + z + 3 * x) ≤ 1 / 7 := by
  have h1 : z = 1 - x - y := by linarith
  rw [h1]
  have h2 : 0 < 1 - x - y := by nlinarith
  have hx1 : 0 < 1 + x + 3 * y := by
    nlinarith
  have hy1 : 0 < 4 - 3 * x - 2 * y := by
    nlinarith [h2]
  have hz1 : 0 < 2 + 2 * x - y := by
    nlinarith [h2]
  have h3 : x * (2 * y - (1 - x - y)) / (1 + x + 3 * y) + y * (2 * (1 - x - y) - x) / (1 + y + 3 * (1 - x - y)) + (1 - x - y) * (2 * x - y) / (1 + (1 - x - y) + 3 * x) - 1 / 7 ≤ 0 := by
    have h4 : x * (2 * y - (1 - x - y)) / (1 + x + 3 * y) + y * (2 * (1 - x - y) - x) / (1 + y + 3 * (1 - x - y)) + (1 - x - y) * (2 * x - y) / (1 + (1 - x - y) + 3 * x) - 1 / 7 = 
      (x * (2 * y - (1 - x - y)) * (4 - 3 * x - 2 * y) * (2 + 2 * x - y) + 
      y * (2 * (1 - x - y) - x) * (1 + x + 3 * y) * (2 + 2 * x - y) + 
      (1 - x - y) * (2 * x - y) * (1 + x + 3 * y) * (4 - 3 * x - 2 * y) - 
      1 / 7 * (1 + x + 3 * y) * (4 - 3 * x - 2 * y) * (2 + 2 * x - y)) / 
      ((1 + x + 3 * y) * (4 - 3 * x - 2 * y) * (2 + 2 * x - y)) := by 
      field_simp 
      ring 
    rw [h4] 
    apply div_nonpos_of_nonpos_of_nonneg 
    -- Prove the numerator is nonpositive 
    nlinarith [sq_nonneg (x - 1 / 7), sq_nonneg (y - 2 / 7), sq_nonneg (1 - x - y - 4 / 7), 
              sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), 
              mul_pos hx hy, mul_pos hx (show (0 : ℝ) < 1 - x - y by nlinarith), 
              mul_pos hy (show (0 : ℝ) < 1 - x - y by nlinarith)
    ] 
    -- Prove the denominator is nonnegative 
    all_goals 
      positivity 
  linarith [h3]