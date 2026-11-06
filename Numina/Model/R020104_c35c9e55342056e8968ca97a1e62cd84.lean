import Mathlib

theorem inequalities_33955 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1) :
    1 - (x ^ 2 - y * z) / (x ^ 2 + x) = ((1 - y) * (1 - z)) / (x ^ 2 + x) ∧
    (x ^ 2 - y * z) / (x ^ 2 + x) + (y ^ 2 - z * x) / (y ^ 2 + y) +
    (z ^ 2 - x * y) / (z ^ 2 + z) ≤ 0 := by
  constructor
  · -- Prove 1 - (x ^ 2 - y * z) / (x ^ 2 + x) = ((1 - y) * (1 - z)) / (x ^ 2 + x)
    have h1 : x ^ 2 + x > 0 := by
      nlinarith
    have h2 : x + y * z = (1 - y) * (1 - z) := by
      have hx' : x = 1 - y - z := by linarith
      rw [hx']
      nlinarith 
    have h3 : 1 - (x ^ 2 - y * z) / (x ^ 2 + x) = ((1 - y) * (1 - z)) / (x ^ 2 + x) := by
      have eq1 : 1 - (x ^ 2 - y * z) / (x ^ 2 + x) = (x ^ 2 + x - (x ^ 2 - y * z) ) / (x ^ 2 + x) := by
        field_simp [h1]
      have eq2 : x ^ 2 + x - (x ^ 2 - y * z) = x + y * z := by
        nlinarith
      rw [eq1, eq2]
      have eq3 : x + y * z = (1 - y) * (1 - z) := by
        nlinarith [h2]
      rw [eq3]
    exact h3
  · -- Prove (x ^ 2 - y * z) / (x ^ 2 + x) + (y ^ 2 - z * x) / (y ^ 2 + y) + (z ^ 2 - x * y) / (z ^ 2 + z) ≤ 0
    have h1 : x ^ 2 + x > 0 := by
      nlinarith
    have h2 : y ^ 2 + y > 0 := by
      nlinarith
    have h3 : z ^ 2 + z > 0 := by
      nlinarith 
    have h4 : (x ^ 2 - y * z) / (x ^ 2 + x) + (y ^ 2 - z * x) / (y ^ 2 + y) + (z ^ 2 - x * y) / (z ^ 2 + z) ≤ 0 := by
      have h4 : (x ^ 2 - y * z) / (x ^ 2 + x) + (y ^ 2 - z * x) / (y ^ 2 + y) + (z ^ 2 - x * y) / (z ^ 2 + z) =
          ((x ^ 2 - y * z) * (y ^ 2 + y) * (z ^ 2 + z) + (y ^ 2 - z * x) * (x ^ 2 + x) * (z ^ 2 + z) + (z ^ 2 - x * y) * (x ^ 2 + x) * (y ^ 2 + y)) / ((x ^ 2 + x) * (y ^ 2 + y) * (z ^ 2 + z)) := by
        field_simp 
        ring 
      rw [h4]
      apply div_nonpos_of_nonpos_of_nonneg 
      · -- Show numerator is non-positive
        nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
        ]
      · -- Show denominator is non-negative
        positivity 
    linarith