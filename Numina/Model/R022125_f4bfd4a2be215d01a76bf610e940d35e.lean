import Mathlib

theorem inequalities_321550 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 1) :
    0 ≤ x * y + y * z + z * x - 2 * x * y * z ∧ x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27 := by
  constructor
  · -- Prove 0 ≤ x * y + y * z + z * x - 2 * x * y * z
    have h1 : z = 1 - x - y := by linarith
    rw [h1]
    -- Prove 0 ≤ (x * y + y * (1 - x - y) + x * (1 - x - y) - 2 * x * y * (1 - x - y))
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
          mul_nonneg hx hy, mul_nonneg hy (show 0 ≤ (1 - x - y) by nlinarith), 
          mul_nonneg hx (show 0 ≤ (1 - x - y) by nlinarith), 
          sq_nonneg (x + y - (1 - x - y)), sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y))
        ]
  · -- Prove x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27
    have h1 : z = 1 - x - y := by linarith
    rw [h1]
    -- Prove (x * y + y * (1 - x - y) + x * (1 - x - y) - 2 * x * y * (1 - x - y)) ≤ 7 / 27
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
          mul_nonneg hx hy, mul_nonneg hy (show 0 ≤ (1 - x - y) by nlinarith), 
          mul_nonneg hx (show 0 ≤ (1 - x - y) by nlinarith), 
          sq_nonneg (x + y - (1 - x - y)), sq_nonneg (x - y), sq_nonneg (x - 1/3), sq_nonneg (y - 1/3), sq_nonneg ((1 - x - y) - 1/3), 
          mul_nonneg (show 0 ≤ (1 - x - y) by nlinarith) (show 0 ≤ (1 - x - y) by nlinarith)
        ]