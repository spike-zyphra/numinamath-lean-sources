import Mathlib

theorem inequalities_149510 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (4 * x + y) / 6 ≥ (x ^ 2 * y / 2) ^ ((1 : ℝ) / 3) := by
  have h1 : 0 < x ^ 2 * y / 2 := by
    positivity
  have h5 : (x ^ 2 * y / 2) ≥ 0 := by positivity
  have h6 : (x ^ 2 * y / 2) ^ ((1 : ℝ) / 3) ≥ 0 := by positivity
  have h7 : ((4 * x + y) / 6) ≥ (x ^ 2 * y / 2) ^ ((1 : ℝ) / 3) := by
    have h8 : ((4 * x + y) / 6) ^ 3 ≥ (x ^ 2 * y / 2) := by
      nlinarith [sq_nonneg (x - y / 2), sq_nonneg (y - 2 * x), sq_nonneg (x - 1), sq_nonneg (y - 2), sq_nonneg (x - y), sq_nonneg ((4 * x + y) / 6), sq_nonneg (x * y), sq_nonneg (x - y / 2), sq_nonneg (y - x * 4), sq_nonneg (x - 2 * x), sq_nonneg (y * (x - y)), sq_nonneg (y * (4 * x + y)), sq_nonneg ((4 * x + y) * x * y), sq_nonneg ((4 * x + y) ^ 2), sq_nonneg (y ^ 2 - 4 * x ^ 2), sq_nonneg (x ^ 2 - y / 2 ^ 2), sq_nonneg (y ^ 2 - (4 * x + y) ^ 2), mul_pos hx hy]
    have h11 : ((4 * x + y) / 6) ≥ (0 : ℝ) := by positivity
    have h12 : (x ^ 2 * y / 2) ^ ((1 : ℝ) / 3) ≥ (0 : ℝ) := by positivity
    have h13 : (( (4 * x + y) / 6 ) ) ≥ ( (x ^ 2 * y / 2 ) ^ ((1 : ℝ) / 3) ) := by
      have h14 : ( ( (4 * x + y ) / 6 ) ^ 3 ) ≥ ( (x ^ 2 * y / 2 ) ) := h8
      have h17 : ( ( (x ^ 2 * y / 2 ) ^ ((1 : ℝ) / 3 ) ) ) ^ 3 = (x ^ 2 * y / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals
          try positivity
          try nlinarith
      have h21 : ( ( (4 * x + y ) / 6 ) ) ≥ ( ( (x ^ 2 * y / 2 ) ^ ((1 : ℝ) / 3 ) ) ) := by
        by_contra h
        push_neg at h
        have h24 : ( ( (4 * x + y ) / 6 ) ) < ( ( (x ^ 2 * y / 2 ) ^ ((1 : ℝ) / 3 ) ) ) := by linarith
        have h25 : ( ( (4 * x + y ) / 6 ) ) ^ 3 < ( ( (x ^ 2 * y / 2 ) ^ ((1 : ℝ) / 3 ) ) ) ^ 3 := by
          apply pow_lt_pow_left
          all_goals
            try nlinarith
            try linarith
        have h26 : ( ( (x ^ 2 * y / 2 ) ^ ((1 : ℝ) / 3 ) ) ) ^ 3 = (x ^ 2 * y / 2) := h17
        nlinarith [h26, h25, h14]
      assumption
    assumption
  linarith