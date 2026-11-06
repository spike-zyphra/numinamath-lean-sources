import Mathlib

theorem inequalities_600210 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 1) :
    0 ≤ y * z + z * x + x * y - 2 * x * y * z ∧ y * z + z * x + x * y - 2 * x * y * z ≤ 7 / 27 := by
  constructor
  · -- First part: prove $0 \leqslant yz + z x + x y - 2 x y z$
    have h1 : z = 1 - x - y := by linarith
    rw [h1]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
      mul_nonneg hx hy, mul_nonneg hy (show 0 ≤ 1 - x - y by nlinarith), 
      mul_nonneg (show 0 ≤ 1 - x - y by nlinarith) hx
    ]
  · -- Second part: prove $y z + z x + x y - 2 x y z \leq \frac{7}{27}$
    have h1 : z = 1 - x - y := by linarith
    rw [h1]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
      sq_nonneg (x + y - (1 - x - y)), 
      mul_nonneg hx hy, mul_nonneg hy (show 0 ≤ 1 - x - y by nlinarith), 
      mul_nonneg (show 0 ≤ 1 - x - y by nlinarith) hx, 
      sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg ((1 - x - y) - 1 / 3)
    ]