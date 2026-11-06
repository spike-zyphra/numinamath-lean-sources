import Mathlib

theorem inequalities_207914 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 1) :
    2 * (x ^ 2 + y ^ 2 + z ^ 2) + 9 * x * y * z ≥ 1 ∧
    x * y + y * z + z * x - 3 * x * y * z ≤ 1 / 4 := by
  constructor
  · -- Prove 2 * (x ^ 2 + y ^ 2 + z ^ 2) + 9 * x * y * z ≥ 1
    have h1 : z = 1 - x - y := by linarith
    rw [h1]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
          sq_nonneg (x + y - (1 - x - y)), 
          mul_nonneg hx hy, 
          mul_nonneg hx (show (0 : ℝ) ≤ 1 - x - y by nlinarith), 
          mul_nonneg hy (show (0 : ℝ) ≤ 1 - x - y by nlinarith), 
          sq_nonneg (x - 1 / 2), 
          sq_nonneg (y - 1 / 2), 
          sq_nonneg ((1 - x - y) - 1 / 2)
        ]
  · -- Prove x * y + y * z + z * x - 3 * x * y * z ≤ 1 / 4
    have h1 : z = 1 - x - y := by linarith
    rw [h1]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
          sq_nonneg (x + y - (1 - x - y)), 
          mul_nonneg hx hy, 
          mul_nonneg hx (show (0 : ℝ) ≤ 1 - x - y by nlinarith), 
          mul_nonneg hy (show (0 : ℝ) ≤ 1 - x - y by nlinarith), 
          sq_nonneg (x - 1 / 2), 
          sq_nonneg (y - 1 / 2), 
          sq_nonneg ((1 - x - y) - 1 / 2)
        ]