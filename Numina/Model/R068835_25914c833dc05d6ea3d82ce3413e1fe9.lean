import Mathlib

open Real

theorem inequalities_83444 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x ≥ y + z) :
    7 ≤ (x + y) / z + (y + z) / x + (z + x) / y := by
  have h1 : 0 < z := hz
  have h2 : 0 < x := hx
  have h3 : 0 < y := hy
  have h4 : 0 < x * y := mul_pos hx hy
  have h5 : 0 < x * z := mul_pos hx hz
  have h6 : 0 < y * z := mul_pos hy hz
  have h7 : 0 < x * y * z := mul_pos h4 hz

  have h8 : (x + y) * (x * y) + (y + z) * (y * z) + (z + x) * (x * z) ≥ 7 * (x * y * z) := by
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y - z), 
          sq_nonneg (y - z), 
          sq_nonneg (x - y), 
          sq_nonneg (x - z), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
          h
          ]

  have h9 : (x + y) / z + (y + z) / x + (z + x) / y - 7 ≥ 0 := by
    have pos1 : 0 < z := hz
    have pos2 : 0 < x := hx
    have pos3 : 0 < y := hy
    have h10 : (x + y) / z + (y + z) / x + (z + x) / y - 7 = 
          ((x + y) * (x * y) + (y + z) * (y * z) + (z + x) * (x * z) - 7 * (x * y * z)) / (x * y * z) := by 
      field_simp [pos1, pos2, pos3]
      ring
    rw [h10]
    have h11 : (x + y) * (x * y) + (y + z) * (y * z) + (z + x) * (x * z) - 7 * (x * y * z) ≥ 0 := by
      linarith [h8]
    apply div_nonneg h11 (by positivity)
  
  linarith