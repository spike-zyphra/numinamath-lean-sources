import Mathlib

theorem inequalities_173422 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (x + y) + y / (y + z) + z / (z + x) ≤ 2 := by

  have h1 : x / (x + y) ≤ (x + z) / (x + y + z) := by
    have denominator1 : 0 < x + y := by linarith
    have denominator2 : 0 < x + y + z := by linarith
    apply (div_le_div_iff (by linarith) (by linarith)).mpr
    have h2 : x * (x + y + z) ≤ (x + z) * (x + y) := by
      nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    linarith [h2]

  have h2 : y / (y + z) ≤ (y + x) / (x + y + z) := by
    have denominator1 : 0 < y + z := by linarith
    have denominator2 : 0 < x + y + z := by linarith
    apply (div_le_div_iff (by linarith) (by linarith)).mpr
    have h3 : y * (x + y + z) ≤ (y + x) * (y + z) := by
      nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    linarith [h3]

  have h3 : z / (z + x) ≤ (z + y) / (x + y + z) := by
    have denominator1 : 0 < z + x := by linarith
    have denominator2 : 0 < x + y + z := by linarith
    apply (div_le_div_iff (by linarith) (by linarith)).mpr
    have h4 : z * (x + y + z) ≤ (z + y) * (z + x) := by
      nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    linarith [h4]

  have h4 : x / (x + y) + y / (y + z) + z / (z + x) ≤ (x + z) / (x + y + z) + (y + x) / (x + y + z) + (z + y) / (x + y + z) := by
    linarith [h1, h2, h3]

  have h5 : (x + z) / (x + y + z) + (y + x) / (x + y + z) + (z + y) / (x + y + z) = 2 := by
    field_simp
    ring

  linarith [h4, h5]