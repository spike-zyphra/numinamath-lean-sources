import Mathlib

theorem inequalities_318371 (x y z : ℝ) (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1)
    (h : x * y * z = 1) :
    x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 ≥ 1 := by
  have hx1 : x - 1 ≠ 0 := by
    intro h1
    apply hx
    linarith
  have hy1 : y - 1 ≠ 0 := by
    intro h1
    apply hy
    linarith
  have hz1 : z - 1 ≠ 0 := by
    intro h1
    apply hz
    linarith
  have h1 : x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 - 1 ≥ 0 := by
    have h2 : (x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 - 1) = 
      (x^2 * (y - 1)^2 * (z - 1)^2 + y^2 * (x - 1)^2 * (z - 1)^2 + z^2 * (x - 1)^2 * (y - 1)^2 - (x - 1)^2 * (y - 1)^2 * (z - 1)^2) / ((x - 1)^2 * (y - 1)^2 * (z - 1)^2) := by
      field_simp [show x - 1 ≠ 0 by assumption, show y - 1 ≠ 0 by assumption, show z - 1 ≠ 0 by assumption]
      ring
    rw [h2] at *
    have h3 : x^2 * (y - 1)^2 * (z - 1)^2 + y^2 * (x - 1)^2 * (z - 1)^2 + z^2 * (x - 1)^2 * (y - 1)^2 - (x - 1)^2 * (y - 1)^2 * (z - 1)^2 ≥ 0 := by
      nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1), 
              sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
              sq_nonneg (x * y * z - 1), 
              sq_nonneg (x * y + y * z + z * x - 3), 
              sq_nonneg (x + y + z - 3), 
              h, 
              mul_ne_zero hx1 hy1, mul_ne_zero hy1 hz1, mul_ne_zero hx1 hz1
            ]
    have h4 : (x - 1)^2 * (y - 1)^2 * (z - 1)^2 > 0 := by
      positivity
    apply div_nonneg
    linarith [h3]
    all_goals
      positivity
  linarith [h1]