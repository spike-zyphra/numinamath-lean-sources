import Mathlib

theorem inequalities_135198 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 1) :
    0 ≤ x * y + y * z + x * z - 2 * x * y * z ∧
    x * y + y * z + x * z - 2 * x * y * z ≤ 7 / 27 := by
  have h1 : z = 1 - x - y := by linarith 
  rw [h1]
  constructor
  · -- Prove $0 \leq x * y + y * z + x * z - 2 * x * y * z$
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), mul_nonneg hx hy, mul_nonneg hx (show 0 ≤ (1 - x - y : ℝ) by nlinarith), mul_nonneg hy (show 0 ≤ (1 - x - y : ℝ) by nlinarith)]
  · -- Prove $x * y + y * z + x * z - 2 * x * y * z \leq 7 / 27$
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), mul_nonneg hx hy, mul_nonneg hx (show 0 ≤ (1 - x - y : ℝ) by nlinarith), mul_nonneg hy (show 0 ≤ (1 - x - y : ℝ) by nlinarith), sq_nonneg (x + y - (1 - x - y)), sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y))
          ]