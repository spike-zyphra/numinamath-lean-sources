import Mathlib

theorem inequalities_598026 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (a b : ℝ) (ha : 0 ≤ a) (hb : b ∈ Set.univ) :
    0 ≤ (a * y + b * x + b * z) * (y ^ 2 - x ^ 2) / (z + x) +
        (a * z + b * x + b * y) * (z ^ 2 - y ^ 2) / (x + y) +
        (a * x + b * y + b * z) * (x ^ 2 - z ^ 2) / (y + z) := by

  have hx1 : 0 < x := hx
  have hy1 : 0 < y := hy
  have hz1 : 0 < z := hz
  have h1 : 0 < z + x := by linarith
  have h2 : 0 < x + y := by linarith
  have h3 : 0 < y + z := by linarith
  have h4 : (a * y + b * x + b * z) * (y ^ 2 - x ^ 2) / (z + x) +
      (a * z + b * x + b * y) * (z ^ 2 - y ^ 2) / (x + y) +
      (a * x + b * y + b * z) * (x ^ 2 - z ^ 2) / (y + z) ≥ 0 := by
    have pos1 : 0 < (z + x) * (x + y) * (y + z) := by positivity
    have eq1 : (a * y + b * x + b * z) * (y ^ 2 - x ^ 2) / (z + x) +
        (a * z + b * x + b * y) * (z ^ 2 - y ^ 2) / (x + y) +
        (a * x + b * y + b * z) * (x ^ 2 - z ^ 2) / (y + z) =
        ( (a * y + b * x + b * z) * (y ^ 2 - x ^ 2) * (x + y) * (y + z) +
          (a * z + b * x + b * y) * (z ^ 2 - y ^ 2) * (z + x) * (y + z) +
          (a * x + b * y + b * z) * (x ^ 2 - z ^ 2) * (z + x) * (x + y) ) / ((z + x) * (x + y) * (y + z)) := by 
      field_simp
      ring
    rw [eq1] at *
    apply div_nonneg
    · -- Prove the numerator is non-negative
      have eq2 : (a * y + b * x + b * z) * (y ^ 2 - x ^ 2) * (x + y) * (y + z) +
          (a * z + b * x + b * y) * (z ^ 2 - y ^ 2) * (z + x) * (y + z) +
          (a * x + b * y + b * z) * (x ^ 2 - z ^ 2) * (z + x) * (x + y) = a * (y * (y ^ 2 - x ^ 2) * (x + y) * (y + z) + z * (z ^ 2 - y ^ 2) * (z + x) * (y + z) + x * (x ^ 2 - z ^ 2) * (z + x) * (x + y)) := by 
        ring_nf
      rw [eq2]
      have eq3 : y * (y ^ 2 - x ^ 2) * (x + y) * (y + z) + z * (z ^ 2 - y ^ 2) * (z + x) * (y + z) + x * (x ^ 2 - z ^ 2) * (z + x) * (x + y) ≥ 0 := by 
        nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (y - z)), sq_nonneg (x * (z - x)),
          sq_nonneg (y * (x - y)), sq_nonneg (y * (y - z)), sq_nonneg (y * (z - x)),
          sq_nonneg (z * (x - y)), sq_nonneg (z * (y - z)), sq_nonneg (z * (z - x)),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
          mul_pos (show 0 < x * y by nlinarith) (show 0 < z * x by nlinarith), 
          mul_pos (show 0 < y * z by nlinarith) (show 0 < z * x by nlinarith)
        ]
      have eq4 : a * (y * (y ^ 2 - x ^ 2) * (x + y) * (y + z) + z * (z ^ 2 - y ^ 2) * (z + x) * (y + z) + x * (x ^ 2 - z ^ 2) * (z + x) * (x + y)) ≥ 0 := by 
        apply mul_nonneg 
        exact ha 
        linarith [eq3]
      linarith [eq4]
    · -- Prove the denominator is positive
      positivity 
  linarith [h4]