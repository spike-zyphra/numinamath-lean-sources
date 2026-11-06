import Mathlib
open Real

theorem inequalities_8541 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    sqrt (x + y) + sqrt (y + z) + sqrt (z + x) ≥
    4 * (x * y + y * z + z * x) / sqrt ((x + y) * (y + z) * (z + x)):= by
  have h1 : 0 < x + y := by linarith
  have h2 : 0 < y + z := by linarith
  have h3 : 0 < z + x := by linarith
  have h41 : 0 < (x + y) * (y + z) * (z + x) := by positivity
  have h81 : sqrt ((x + y) * (y + z) * (z + x)) > 0 := by positivity
  have h9 : (sqrt (x + y) + sqrt (y + z) + sqrt (z + x)) * sqrt ((x + y) * (y + z) * (z + x)) ≥ 4 * (x * y + y * z + z * x) := by
    have h7 : sqrt ((x + y) * (y + z) * (z + x)) = sqrt (x + y) * sqrt (y + z) * sqrt (z + x) := by
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    rw [h7] at *
    nlinarith [sq_nonneg (sqrt (x + y) - sqrt (y + z)), sq_nonneg (sqrt (x + y) - sqrt (z + x)), sq_nonneg (sqrt (y + z) - sqrt (z + x)), 
      sq_nonneg (sqrt (x + y) * sqrt (y + z) - sqrt (x + y) * sqrt (z + x)), 
      sq_nonneg (sqrt (x + y) * sqrt (z + x) - sqrt (y + z) * sqrt (z + x)), 
      sq_nonneg (sqrt (y + z) * sqrt (z + x) - sqrt (x + y) * sqrt (y + z)), 
      Real.sq_sqrt (show 0 ≤ (x + y : ℝ) by positivity),
      Real.sq_sqrt (show 0 ≤ (y + z : ℝ) by positivity), 
      Real.sq_sqrt (show 0 ≤ (z + x : ℝ) by positivity),
      sq_nonneg (sqrt (x + y)), sq_nonneg (sqrt (y + z)), sq_nonneg (sqrt (z + x)), 
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
      Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x),
      mul_nonneg (Real.sqrt_nonneg (x + y)) (Real.sqrt_nonneg (y + z)), 
      mul_nonneg (Real.sqrt_nonneg (y + z)) (Real.sqrt_nonneg (z + x)), 
      mul_nonneg (Real.sqrt_nonneg (z + x)) (Real.sqrt_nonneg (x + y)), 
      sq_nonneg ((sqrt (x + y)) * (sqrt (y + z)) - (sqrt (y + z)) * (sqrt (z + x))), 
      sq_nonneg ((sqrt (x + y)) * (sqrt (z + x)) - (sqrt (y + z)) * (sqrt (z + x)))
    ]
  have h31 : sqrt (x + y) + sqrt (y + z) + sqrt (z + x) ≥ 4 * (x * y + y * z + z * x) / sqrt ((x + y) * (y + z) * (z + x)):= by
    have h13 : sqrt ((x + y) * (y + z) * (z + x)) > 0 := h81
    have h21 : (sqrt (x + y) + sqrt (y + z) + sqrt (z + x)) * sqrt ((x + y) * (y + z) * (z + x)) ≥ 4 * (x * y + y * z + z * x) := h9
    -- Let's prove the goal by rearranging the inequality
    have h43 : (sqrt (x + y) + sqrt (y + z) + sqrt (z + x)) ≥ (4 * (x * y + y * z + z * x) / sqrt ((x + y) * (y + z) * (z + x))) := by
      have h44 : sqrt ((x + y) * (y + z) * (z + x)) > 0 := h13
      apply (div_le_iff₀ (by positivity)).mpr 
      nlinarith [h21, Real.sqrt_nonneg (x + y), Real.sqrt_nonneg (y + z), Real.sqrt_nonneg (z + x), 
        Real.sqrt_nonneg ((x + y) * (y + z) * (z + x)), 
          mul_nonneg (Real.sqrt_nonneg (x + y)) (Real.sqrt_nonneg (y + z)), 
            mul_nonneg (Real.sqrt_nonneg (x + y)) (Real.sqrt_nonneg (z + x)), 
              mul_nonneg (Real.sqrt_nonneg (y + z)) (Real.sqrt_nonneg (z + x))
        ]
    linarith
  linarith [h31]