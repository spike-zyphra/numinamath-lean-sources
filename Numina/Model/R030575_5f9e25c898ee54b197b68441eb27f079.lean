import Mathlib


theorem algebra_110 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x * y + y * z + z * x ≠ 1) (h2 : (x ^ 2 - 1) * (y ^ 2 - 1) / (x * y) +
    (y ^ 2 - 1) * (z ^ 2 - 1) / (y * z) + (z ^ 2 - 1) * (x ^ 2 - 1) / (z * x) = 4) :
    1 / (x * y) + 1 / (y * z) + 1 / (z * x) = 1 := by

  have pos1 : 0 < x * y := mul_pos hx hy
  have pos2 : 0 < y * z := mul_pos hy hz
  have pos3 : 0 < z * x := mul_pos hz hx
  have pos4 : 0 < x * y * z := mul_pos (mul_pos hx hy) hz

  have eq1 : z * ((x ^ 2 - 1) * (y ^ 2 - 1)) + x * ((y ^ 2 - 1) * (z ^ 2 - 1)) + y * ((z ^ 2 - 1) * (x ^ 2 - 1)) = 4 * (x * y * z) := by
    have h3 : (x ^ 2 - 1) * (y ^ 2 - 1) / (x * y) + (y ^ 2 - 1) * (z ^ 2 - 1) / (y * z) + (z ^ 2 - 1) * (x ^ 2 - 1) / (z * x) = 4 := by
      linarith [h2]
    have h4 : ((x ^ 2 - 1) * (y ^ 2 - 1) / (x * y) + (y ^ 2 - 1) * (z ^ 2 - 1) / (y * z) + (z ^ 2 - 1) * (x ^ 2 - 1) / (z * x)) * (x * y * z) = 4 * (x * y * z) := by
      rw [h3]
      all_goals nlinarith
    have eq2 : ((x ^ 2 - 1) * (y ^ 2 - 1) / (x * y) + (y ^ 2 - 1) * (z ^ 2 - 1) / (y * z) + (z ^ 2 - 1) * (x ^ 2 - 1) / (z * x)) * (x * y * z) =
        z * ((x ^ 2 - 1) * (y ^ 2 - 1)) + x * ((y ^ 2 - 1) * (z ^ 2 - 1)) + y * ((z ^ 2 - 1) * (x ^ 2 - 1)) := by 
      field_simp [show 0 < x * y by positivity, show 0 < y * z by positivity, show 0 < z * x by positivity]
      all_goals ring
    rw [eq2] at h4
    linarith [h4]

  have eq2 : (x * y * z - (x + y + z)) * (x * y + y * z + z * x - 1) = 0 := by
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]

  cases' (mul_eq_zero.1 eq2) with h3 h4
  · 
    have h5 : x * y * z = x + y + z := by linarith
    have h7 : 1 / (x * y) + 1 / (y * z) + 1 / (z * x) = (x + y + z) / (x * y * z) := by
      field_simp [show 0 < x * y by positivity, show 0 < y * z by positivity, show 0 < z * x by positivity]
      all_goals ring
    rw [h7]
    have h8 : (x + y + z) / (x * y * z) = 1 := by
      rw [show x * y * z = x + y + z by linarith [h5]]
      field_simp [pos4]
    linarith [h8]

  · 
    have h5 : x * y + y * z + z * x = 1 := by linarith
    exfalso
    apply h1
    linarith [h5]