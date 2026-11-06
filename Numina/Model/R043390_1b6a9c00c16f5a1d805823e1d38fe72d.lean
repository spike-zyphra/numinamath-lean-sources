import Mathlib

theorem inequalities_600650 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z = 1) :
    3 / 4 ≤ x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) +
    z ^ 3 / ((1 + x) * (1 + y)) := by
  have h1 : 0 < (1 + y) * (1 + z) := by positivity
  have h2 : 0 < (1 + z) * (1 + x) := by positivity
  have h3 : 0 < (1 + x) * (1 + y) := by positivity
  have h4 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 ≥ 0 := by
    have h5 : 0 < (1 + x) * (1 + y) * (1 + z) := by positivity
    have h6 : (x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4) =
        (x ^ 3 * (1 + x) + y ^ 3 * (1 + y) + z ^ 3 * (1 + z) - 3 / 4 * ((1 + x) * (1 + y) * (1 + z)) ) / ((1 + x) * (1 + y) * (1 + z)) := by
      field_simp
      ring
    rw [h6]
    have h7 : x ^ 3 * (1 + x) + y ^ 3 * (1 + y) + z ^ 3 * (1 + z) - 3 / 4 * ((1 + x) * (1 + y) * (1 + z)) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, h, mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith), 
          mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ z by linarith), 
          mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ x by linarith)]
    apply div_nonneg
    · linarith
    · positivity
  linarith
  all_goals try { tauto }