import Mathlib

theorem inequalities_599459
    (x y z : ℝ)
    (hx : 0 < x ∧ x ≤ 1)
    (hy : 0 < y ∧ y ≤ 1)
    (hz : 0 < z ∧ z ≤ 1) :
    x / (1 + y + z * x) + y / (1 + z + x * y) + z / (1 + x + y * z) ≤
    3 / (x + y + z) := by
  have hx0 : 0 < x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have hy0 : 0 < y := hy.1
  have hy1 : y ≤ 1 := hy.2
  have hz0 : 0 < z := hz.1
  have hz1 : z ≤ 1 := hz.2
  have h1 : x / (1 + y + z * x) ≤ 1 / (x + y + z) := by
    have h2 : 0 < 1 + y + z * x := by
      nlinarith
    have h3 : 0 < x + y + z := by
      nlinarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ 1 - y by linarith),
      mul_nonneg (show 0 ≤ 1 - y by linarith) (show 0 ≤ 1 - z by linarith),
      mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ 1 - z by linarith)]
  have h2 : y / (1 + z + x * y) ≤ 1 / (x + y + z) := by
    have h4 : 0 < 1 + z + x * y := by
      nlinarith
    have h3 : 0 < x + y + z := by
      nlinarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (y - 1), sq_nonneg (x - 1), sq_nonneg (z - 1),
      mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ 1 - y by linarith),
      mul_nonneg (show 0 ≤ 1 - y by linarith) (show 0 ≤ 1 - z by linarith),
      mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ 1 - z by linarith)]
  have h3 : z / (1 + x + y * z) ≤ 1 / (x + y + z) := by
    have h4 : 0 < 1 + x + y * z := by
      nlinarith
    have h3 : 0 < x + y + z := by
      nlinarith
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (z - 1), sq_nonneg (x - 1), sq_nonneg (y - 1),
      mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ 1 - y by linarith),
      mul_nonneg (show 0 ≤ 1 - y by linarith) (show 0 ≤ 1 - z by linarith),
      mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ 1 - z by linarith)]
  have h4 : x / (1 + y + z * x) + y / (1 + z + x * y) + z / (1 + x + y * z) ≤ 3 / (x + y + z) := by
    have h5 : x / (1 + y + z * x) + y / (1 + z + x * y) + z / (1 + x + y * z) ≤ 1 / (x + y + z) + 1 / (x + y + z) + 1 / (x + y + z) := by
      linarith [h1, h2, h3]
    have h6 : 1 / (x + y + z) + 1 / (x + y + z) + 1 / (x + y + z) = 3 / (x + y + z) := by
      ring
    linarith
  exact h4