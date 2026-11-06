import Mathlib


theorem inequalities_90439 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x < 1) (hyz : y < 1) (hzz : z < 1)
    (h : x ^ 2 / (1 - x) + y ^ 2 / (1 - y) + z ^ 2 / (1 - z) ≤ 3 / 2) :
    1 / (1 - x) + 1 / (1 - y) + 1 / (1 - z) ≤ 6 := by

  have hx1 : 0 < 1 - x := by linarith
  have hy1 : 0 < 1 - y := by linarith
  have hz1 : 0 < 1 - z := by linarith


  have h1 : x ^ 2 / (1 - x) ≥ 3 * x - 1 := by
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - 1)]
  have h2 : y ^ 2 / (1 - y) ≥ 3 * y - 1 := by
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (y - 1 / 2), sq_nonneg (y - 1)]
  have h3 : z ^ 2 / (1 - z) ≥ 3 * z - 1 := by
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [sq_nonneg (z - 1 / 2), sq_nonneg (z - 1)]
  have h4 : x ^ 2 / (1 - x) + y ^ 2 / (1 - y) + z ^ 2 / (1 - z) ≥ 3 * (x + y + z) - 3 := by
    linarith [h1, h2, h3]
  have h5 : x + y + z ≤ 3 / 2 := by
    nlinarith [h4, h]

  have eq1 : 1 / (1 - x) = x ^ 2 / (1 - x) + (1 + x) := by
    field_simp [show 1 - x ≠ 0 by linarith]
    nlinarith
  have eq2 : 1 / (1 - y) = y ^ 2 / (1 - y) + (1 + y) := by
    field_simp [show 1 - y ≠ 0 by linarith]
    nlinarith
  have eq3 : 1 / (1 - z) = z ^ 2 / (1 - z) + (1 + z) := by
    field_simp [show 1 - z ≠ 0 by linarith]
    nlinarith

  calc
    1 / (1 - x) + 1 / (1 - y) + 1 / (1 - z) = (x ^ 2 / (1 - x) + (1 + x)) + (y ^ 2 / (1 - y) + (1 + y)) + (z ^ 2 / (1 - z) + (1 + z)) := by
      rw [eq1, eq2, eq3]
    _ = (x ^ 2 / (1 - x) + y ^ 2 / (1 - y) + z ^ 2 / (1 - z)) + ((1 + x) + (1 + y) + (1 + z)) := by
      ring
    _ ≤ (3 / 2) + ((1 + x) + (1 + y) + (1 + z)) := by
      have h7 : x ^ 2 / (1 - x) + y ^ 2 / (1 - y) + z ^ 2 / (1 - z) ≤ 3 / 2 := by linarith [h]
      linarith
    _ = (3 / 2) + (3 + (x + y + z)) := by
      ring
    _ ≤ (3 / 2) + (3 + (3 / 2)) := by
      have h8 : x + y + z ≤ 3 / 2 := h5
      linarith
    _ = (6 : ℝ) := by
      norm_num