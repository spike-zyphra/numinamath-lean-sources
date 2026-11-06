import Mathlib

theorem inequalities_597546 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    3 / 4 ≤ x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) +
    z ^ 3 / ((1 + x) * (1 + y)) := by
  have hx1 : 0 < x := hx
  have hy1 : 0 < y := hy
  have hz1 : 0 < z := hz
  have hx2 : 0 < 1 + x := by linarith
  have hy2 : 0 < 1 + y := by linarith
  have hz2 : 0 < 1 + z := by linarith
  have h1 : 0 < (1 + x) * (1 + y) * (1 + z) := by
    positivity
  have h2 : x ^ 3 * (1 + x) + y ^ 3 * (1 + y) + z ^ 3 * (1 + z) ≥ (3 / 4) * (1 + x) * (1 + y) * (1 + z) := by 
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      hxyz, mul_pos hx1 hy1, mul_pos hy1 hz1, mul_pos hz1 hx1]
  have h3 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) = (x ^ 3 * (1 + x) + y ^ 3 * (1 + y) + z ^ 3 * (1 + z)) / ((1 + x) * (1 + y) * (1 + z)) := by 
    field_simp
    <;> ring
  have h4 : (x ^ 3 * (1 + x) + y ^ 3 * (1 + y) + z ^ 3 * (1 + z)) / ((1 + x) * (1 + y) * (1 + z)) ≥ (3 / 4) := by 
    apply (le_div_iff₀' (by positivity)).mpr
    linarith
  linarith [h3, h4, h2]