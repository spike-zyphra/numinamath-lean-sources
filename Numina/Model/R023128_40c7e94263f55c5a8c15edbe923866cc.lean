import Mathlib

open Real

theorem inequalities_206865 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    sqrt (x ^ 2 + 3 * y ^ 2) + sqrt (x ^ 2 + z ^ 2 + x * z) >
    sqrt (z ^ 2 + 3 * y ^ 2 + 3 * y * z) := by
  have h1 : 0 < x ^ 2 + 3 * y ^ 2 := by nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy]
  have h2 : 0 < x ^ 2 + z ^ 2 + x * z := by nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hz, mul_pos hx hz]
  have h3 : 0 < z ^ 2 + 3 * y ^ 2 + 3 * y * z := by nlinarith [sq_pos_of_pos hz, sq_pos_of_pos hy, mul_pos hy hz]
  have h4 : sqrt (x ^ 2 + 3 * y ^ 2) + sqrt (x ^ 2 + z ^ 2 + x * z) > sqrt (z ^ 2 + 3 * y ^ 2 + 3 * y * z) := by
    have h5 : (sqrt (x ^ 2 + 3 * y ^ 2) + sqrt (x ^ 2 + z ^ 2 + x * z)) ^ 2 > z ^ 2 + 3 * y ^ 2 + 3 * y * z := by
      have h6 : sqrt (x ^ 2 + 3 * y ^ 2) ^ 2 = x ^ 2 + 3 * y ^ 2 := by
        rw [Real.sq_sqrt]
        nlinarith
      have h7 : sqrt (x ^ 2 + z ^ 2 + x * z) ^ 2 = x ^ 2 + z ^ 2 + x * z := by
        rw [Real.sq_sqrt]
        nlinarith
      have h8 : sqrt (x ^ 2 + 3 * y ^ 2) * sqrt (x ^ 2 + z ^ 2 + x * z) > 0 := by
        apply mul_pos
        · -- Show sqrt (x^2 + 3 * y^2) > 0
          apply Real.sqrt_pos.mpr
          nlinarith
        · -- Show sqrt (x^2 + z^2 + x * z) > 0
          apply Real.sqrt_pos.mpr
          nlinarith
      nlinarith [Real.sqrt_nonneg (x ^ 2 + 3 * y ^ 2), Real.sqrt_nonneg (x ^ 2 + z ^ 2 + x * z),
          sq_nonneg (x * y - y * z), sq_nonneg (x - z), sq_nonneg (x * z - 3 * y ^ 2),
          h6, h7, Real.mul_self_sqrt (show 0 ≤ x ^ 2 + 3 * y ^ 2 by nlinarith), Real.mul_self_sqrt (show 0 ≤ x ^ 2 + z ^ 2 + x * z by nlinarith),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
        ]
    have h5' : (sqrt (x ^ 2 + 3 * y ^ 2) + sqrt (x ^ 2 + z ^ 2 + x * z) ) ^ 2 > (sqrt (z ^ 2 + 3 * y ^ 2 + 3 * y * z)) ^ 2 := by
      have h9 : (sqrt (z ^ 2 + 3 * y ^ 2 + 3 * y * z) ) ^ 2 = z ^ 2 + 3 * y ^ 2 + 3 * y * z := by
        rw [Real.sq_sqrt]
        nlinarith
      nlinarith [h5, h9, Real.sqrt_pos.mpr (show 0 < z ^ 2 + 3 * y ^ 2 + 3 * y * z by nlinarith)]
    have h10 : sqrt (x ^ 2 + 3 * y ^ 2) + sqrt (x ^ 2 + z ^ 2 + x * z) > sqrt (z ^ 2 + 3 * y ^ 2 + 3 * y * z) := by
      have h11 : sqrt (x ^ 2 + 3 * y ^ 2) + sqrt (x ^ 2 + z ^ 2 + x * z) > 0 := by positivity
      have h12 : sqrt (z ^ 2 + 3 * y ^ 2 + 3 * y * z) > 0 := by positivity
      nlinarith [h5', Real.sqrt_nonneg (x ^ 2 + 3 * y ^ 2), Real.sqrt_nonneg (x ^ 2 + z ^ 2 + x * z), Real.sqrt_nonneg (z ^ 2 + 3 * y ^ 2 + 3 * y * z)]
    exact h10
  exact h4