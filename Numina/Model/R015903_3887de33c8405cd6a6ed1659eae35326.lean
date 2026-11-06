import Mathlib

open Real

theorem inequalities_114645 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 2 * x + 3 * y + 4 * z = 6) :
    sqrt (2 * x) + sqrt (3 * y) + sqrt (4 * z) < 9 / 2 ∧
    2 / x + 3 / y + 4 / z ≥ 27 / 2 := by

  have h1 : sqrt (2 * x) + sqrt (3 * y) + sqrt (4 * z) < 9 / 2 := by
    nlinarith [sq_nonneg (sqrt (2 * x) - sqrt (3 * y)), sq_nonneg (sqrt (2 * x) - sqrt (4 * z)), sq_nonneg (sqrt (3 * y) - sqrt (4 * z)), 
            Real.sq_sqrt (show 0 ≤ (2 * x : ℝ) by linarith), 
            Real.sq_sqrt (show 0 ≤ (3 * y : ℝ) by linarith), 
            Real.sq_sqrt (show 0 ≤ (4 * z : ℝ) by linarith), 
            Real.sqrt_nonneg (2 * x), Real.sqrt_nonneg (3 * y), Real.sqrt_nonneg (4 * z),
            mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
]
  have h2 : 2 / x + 3 / y + 4 / z ≥ 27 / 2 := by
    have h5 : (2 / x + 3 / y + 4 / z) - 27 / 2 ≥ 0 := by 
      have h4 : 0 < x * y * z := by
        positivity
      have h5 : (2 / x + 3 / y + 4 / z) - 27 / 2 =
          (4 * y * z + 6 * x * z + 8 * x * y - 27 * (x * y * z)) / (2 * x * y * z) := by 
          field_simp 
          ring 
      rw [h5] at *
      apply div_nonneg
      nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), sq_nonneg (z - 2 / 3), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          sq_nonneg (x * y - (2 / 3) * (2 / 3)), 
          sq_nonneg (x * z - (2 / 3) * (2 / 3)), 
          sq_nonneg (y * z - (2 / 3) * (2 / 3)), 
          h
          ]
      all_goals
        positivity 
    linarith 
  constructor
  · exact h1 
  · exact h2