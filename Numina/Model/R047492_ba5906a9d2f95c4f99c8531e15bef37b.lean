import Mathlib

theorem inequalities_211502 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 1) :
    0 ≤ x * y + y * z + z * x - 2 * x * y * z ∧
    x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27 := by

  constructor
  · -- Prove the lower bound: $0 ≤ x y + y z + z x - 2 x y * z$
    have h1 : 0 ≤ x * y + y * z + z * x - 2 * x * y * z := by
      have h2 : z = 1 - x - y := by linarith
      rw [h2]
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
        mul_nonneg hx hy, 
        mul_nonneg hy (show 0 ≤ (1 - x - y : ℝ) by nlinarith), 
        mul_nonneg hx (show 0 ≤ (1 - x - y : ℝ) by nlinarith), 
        sq_nonneg (x + y - (1 - x - y))
      ]
    exact h1
  · -- Prove the upper bound: $x * y + y * z + z * x - 2 * x * y * z \leq 7 / 27$
    have h2 : x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27 := by
      have h1 : z = 1 - x - y := by linarith
      rw [h1]
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
        mul_nonneg hx hy, 
        mul_nonneg hy (show 0 ≤ (1 - x - y : ℝ) by nlinarith), 
        mul_nonneg hx (show 0 ≤ (1 - x - y : ℝ) by nlinarith), 
        sq_nonneg (x + y - (1 - x - y)), 
        sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg ((1 - x - y) - 1 / 3)
      ]
    exact h2