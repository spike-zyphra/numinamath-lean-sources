import Mathlib

open Real

theorem inequalities_4042 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x + y - z) * (y + z - x) * (z + x - y) ≤ x * y * z ∧
    (x + y + z = 1 → x * y + y * z + z * x ≤ (9 * x * y * z + 1) / 4) := by
  constructor
  · -- Prove the first inequality: (x + y - z) * (y + z - x) * (z + x - y) ≤ x * y * z
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y - z), sq_nonneg (y + z - x), sq_nonneg (z + x - y),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
  · -- Prove the second implication: If x + y + z = 1, then x * y + y * z + z * x ≤ (9 * x * y * z + 1) / 4
    intro h
    have h1 : z = 1 - x - y := by linarith
    rw [h1]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
      mul_pos hx hy, 
      mul_pos hx (show 0 < 1 - x - y by nlinarith), 
      mul_pos hy (show 0 < 1 - x - y by nlinarith), 
      sq_nonneg (x + y - (1 - x - y)), sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y))
    ]