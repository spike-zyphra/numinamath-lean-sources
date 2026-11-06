import Mathlib

theorem inequalities_209207 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    (1 / (1 + x + x * y) ≤ 1 / 3) ∨ (y / (1 + y + y * z) ≤ 1 / 3) ∨
    (x * z / (1 + z + x * z) ≤ 1 / 3) := by
  by_contra h
  push_neg at h

  have h1 : 1 / (1 + x + x * y) > 1 / 3 := by linarith [h.1]
  have h2 : y / (1 + y + y * z) > 1 / 3 := by linarith [h.2.1]
  have h3 : x * z / (1 + z + x * z) > 1 / 3 := by linarith [h.2.2]

  have h4 : 1 + x + x * y < 3 := by
    by_contra h4
    push_neg at h4
    have h5 : 1 / (1 + x + x * y) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le
      positivity
      all_goals
        nlinarith [h4]
    linarith [h5, h1]

  have h5 : 1 + y + y * z < 3 * y := by
    by_contra h5
    push_neg at h5
    have h6 : y / (1 + y + y * z) ≤ 1 / 3 := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h5]
    linarith [h6, h2]

  have h6 : 1 + z + x * z < 3 * (x * z) := by
    by_contra h6
    push_neg at h6
    have h7 : x * z / (1 + z + x * z) ≤ 1 / 3 := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [h6]
    linarith [h7, h3]
  nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y - 1), sq_nonneg (x * z - 1), 
            mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
            h4, h5, h6, hxyz]