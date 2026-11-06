import Mathlib

theorem inequalities_87485 (x y z t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) :
    x * y * z * t / ((x + y) * (z + t)) ≤ ((x + z) ^ 2 * (y + t) ^ 2) / (4 * (x + y + z + t) ^ 2) := by
  have h1 : 0 < x + y := by nlinarith
  have h2 : 0 < z + t := by nlinarith
  have h3 : 0 < (x + y) * (z + t) := by positivity
  have h4 : 0 < x + y + z + t := by nlinarith
  have h42 : 0 < 4 * (x + y + z + t) ^ 2 := by positivity
  
  have h5 : x * y * z * t * (4 * (x + y + z + t) ^ 2) ≤ (x + z) ^ 2 * (y + t) ^ 2 * ((x + y) * (z + t)) := by
    nlinarith [sq_nonneg (x * y - z * t), sq_nonneg (x * t - y * z), sq_nonneg (x - z), sq_nonneg (y - t), sq_nonneg (x * (y - t) + z * (t - y)), sq_nonneg (y * (z - x) + t * (x - z)), sq_nonneg ((x + z) * y - (x + z) * t), sq_nonneg ((y + t) * x - (y + t) * z), mul_pos hx hy, mul_pos hx hz, mul_pos hx ht, mul_pos hy hz, mul_pos hy ht, mul_pos hz ht, sq_nonneg (x + z - (y + t)), sq_nonneg (x + t - (y + z)), sq_nonneg (x - z + y - t), sq_nonneg (x - z - (y - t))]
    
  have h6 : x * y * z * t / ((x + y) * (z + t)) - ((x + z) ^ 2 * (y + t) ^ 2) / (4 * (x + y + z + t) ^ 2) ≤ 0 := by
    have h7 : 0 < (x + y) * (z + t) * (4 * (x + y + z + t) ^ 2) := by positivity
    have h8 : x * y * z * t / ((x + y) * (z + t)) - ((x + z) ^ 2 * (y + t) ^ 2) / (4 * (x + y + z + t) ^ 2) = (x * y * z * t * (4 * (x + y + z + t) ^ 2) - (x + z) ^ 2 * (y + t) ^ 2 * ((x + y) * (z + t))) / ((x + y) * (z + t) * (4 * (x + y + z + t) ^ 2)) := by
      field_simp
      <;> ring
    rw [h8]
    apply div_nonpos_of_nonpos_of_nonneg
    linarith
    all_goals positivity
  
  linarith [h6]