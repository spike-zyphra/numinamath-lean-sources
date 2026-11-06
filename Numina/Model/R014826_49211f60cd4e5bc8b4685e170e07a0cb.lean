import Mathlib

theorem inequalities_87012 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = x + y + z) :
    x + y + z + 3 ≥ 6 * ((x * y + y * z + z * x) / 3) ^ ((1 : ℝ) / 3) := by
  have h1 : 0 < x * y + y * z + z * x := by
    nlinarith [mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]

  have h3 : (6 * ((x * y + y * z + z * x ) / 3) ^ ((1 : ℝ) / 3)) ^ 3 = 72 * (x * y + y * z + z * x) := by
    calc
      (6 * ((x * y + y * z + z * x ) / 3) ^ ((1 : ℝ) / 3)) ^ 3
          = 6^3 * (( (x * y + y * z + z * x ) / 3 ) ^ ((1 : ℝ) / 3)) ^3 := by ring_nf
      _ = 216 * ( (x * y + y * z + z * x ) / 3 ) := by
        have h5 : (( (x * y + y * z + z * x ) / 3 ) ^ ((1 : ℝ) / 3)) ^3 = ( (x * y + y * z + z * x ) / 3 ) := by 
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          norm_num
          all_goals linarith [show (x * y + y * z + z * x ) / 3 > 0 by positivity]
        rw [h5]
        all_goals norm_num
      _ = 72 * (x * y + y * z + z * x) := by
        ring_nf
        <;> linarith

  have h4 : (x + y + z + 3) ^ 3 ≥ 72 * (x * y + y * z + z * x) := by
    nlinarith [sq_nonneg (x + y + z - 3), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
              h, mul_pos hx hy, mul_pos hy hz, mul_pos hz hx,
              mul_pos hx (show 0 < x by linarith), 
              mul_pos hy (show 0 < y by linarith),
              mul_pos hz (show 0 < z by linarith)]

  have h8 : x + y + z + 3 ≥ 6 * ((x * y + y * z + z * x ) / 3) ^ ((1 : ℝ) / 3) := by
    have h9 : (6 * ((x * y + y * z + z * x ) / 3) ^ ((1 : ℝ) / 3)) ^ 3 = 72 * (x * y + y * z + z * x) := h3
    have h10 : (x + y + z + 3) ^ 3 ≥ 72 * (x * y + y * z + z * x) := h4
    have h11 : x + y + z + 3 ≥ 0 := by
      nlinarith [h, mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
    have h12 : 6 * ((x * y + y * z + z * x ) / 3) ^ ((1 : ℝ) / 3) ≥ 0 := by 
      positivity
    have h13 : (x + y + z + 3) ≥ (6 * ((x * y + y * z + z * x ) / 3) ^ ((1 : ℝ) / 3)) := by
      nlinarith [sq_nonneg ((x + y + z + 3) - (6 * ((x * y + y * z + z * x ) / 3) ^ ((1 : ℝ) / 3))), sq_nonneg ((6 * ((x * y + y * z + z * x ) / 3) ^ ((1 : ℝ) / 3))), sq_nonneg (x + y + z + 3), 
        h10, Real.rpow_nonneg (show 0 ≤ (x * y + y * z + z * x) / 3 by positivity) (1 / 3 : ℝ)]
    linarith
  exact h8