import Mathlib

theorem inequalities_51716 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x) / 6 ≤
    ((x + y + z) / 3) * Real.sqrt ((x ^ 2 + y ^ 2 + z ^ 2) / 3) := by
  have h1 : 0 ≤ ((x + y + z) / 3) * Real.sqrt ((x ^ 2 + y ^ 2 + z ^ 2) / 3) := by
    have h2 : 0 ≤ (x + y + z) / 3 := by
      linarith
    have h3 : 0 ≤ Real.sqrt ((x ^ 2 + y ^ 2 + z ^ 2) / 3) := Real.sqrt_nonneg ((x ^ 2 + y ^ 2 + z ^ 2) / 3)
    nlinarith
  have h3 : ((x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x) / 6) ^ 2 ≤
    ( ((x + y + z) / 3) * Real.sqrt ((x ^ 2 + y ^ 2 + z ^ 2) / 3) ) ^ 2 := by
    have h4 : ( ((x + y + z) / 3) * Real.sqrt ((x ^ 2 + y ^ 2 + z ^ 2) / 3) ) ^ 2 =
      ( (x + y + z) / 3 ) ^ 2 * ( (x ^ 2 + y ^ 2 + z ^ 2) / 3 ) := by
      calc
        ( ((x + y + z) / 3) * Real.sqrt ((x ^ 2 + y ^ 2 + z ^ 2) / 3) ) ^ 2
          = ( (x + y + z) / 3 ) ^ 2 * ( Real.sqrt ((x ^ 2 + y ^ 2 + z ^ 2) / 3) ) ^ 2 := by ring
        _ = ( (x + y + z) / 3 ) ^ 2 * ( (x ^ 2 + y ^ 2 + z ^ 2) / 3 ) := by
          rw [Real.sq_sqrt]
          positivity
    have h5 : ( (x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x) / 6 ) ^ 2 ≤
      ( (x + y + z) / 3 ) ^ 2 * ( (x ^ 2 + y ^ 2 + z ^ 2) / 3 ) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y + z - (x ^ 2 + y ^ 2 + z ^ 2) / (x + y + z)), 
          Real.sqrt_nonneg ((x ^ 2 + y ^ 2 + z ^ 2) / 3),
          sq_nonneg (x - y + z), sq_nonneg (x + y - z), 
          sq_nonneg (-x + y + z), 
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith), 
          mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ z by linarith), 
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ z by linarith)
        ]
    rw [h4]
    linarith [h5, Real.sqrt_nonneg ((x ^ 2 + y ^ 2 + z ^ 2) / 3)]
  have h4 : (x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x) / 6 ≥ 0 := by
    positivity
  have h5 : ((x + y + z) / 3) * Real.sqrt ((x ^ 2 + y ^ 2 + z ^ 2) / 3) ≥ 0 := by
    nlinarith [ Real.sqrt_nonneg ((x ^ 2 + y ^ 2 + z ^ 2) / 3) ]
  nlinarith [ Real.sqrt_nonneg ((x ^ 2 + y ^ 2 + z ^ 2) / 3), 
          sq_nonneg ( (x ^ 2 + y ^ 2 + z ^ 2 + x * y + y * z + z * x) / 6 - ((x + y + z) / 3) * Real.sqrt ((x ^ 2 + y ^ 2 + z ^ 2) / 3) ), 
          h4, h5 
        ]