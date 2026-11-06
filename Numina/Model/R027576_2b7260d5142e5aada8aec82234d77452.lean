import Mathlib

theorem inequalities_140387 (x y z : ℝ) (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1)
    (hxyz : x * y * z = 1) :
    1 ≤ x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 := by
  have hx1 : x - 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hy1 : y - 1 ≠ 0 := by
    intro h
    apply hy
    linarith
  have hz1 : z - 1 ≠ 0 := by
    intro h
    apply hz
    linarith
  have h1 : 0 < (x - 1) ^ 2 := by
    apply pow_two_pos_of_ne_zero
    exact hx1
  have h2 : 0 < (y - 1) ^ 2 := by
    apply pow_two_pos_of_ne_zero
    exact hy1
  have h3 : 0 < (z - 1) ^ 2 := by
    apply pow_two_pos_of_ne_zero
    exact hz1
  have h4 : x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 - 1 ≥ 0 := by
    have pos1 : 0 < (x - 1) ^ 2 * (y - 1) ^ 2 * (z - 1) ^ 2 := by
      positivity
    have eq1 : x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 - 1 =
      (x^2 * (y - 1) ^ 2 * (z - 1) ^ 2 + y^2 * (x - 1) ^ 2 * (z - 1) ^ 2 + z^2 * (x - 1) ^ 2 * (y - 1) ^ 2 - (x - 1) ^ 2 * (y - 1) ^ 2 * (z - 1) ^ 2) / ((x - 1) ^ 2 * (y - 1) ^ 2 * (z - 1) ^ 2) := by
      field_simp [hx1, hy1, hz1]
      ring
    rw [eq1] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
        sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        sq_nonneg (x + y + z - 3), sq_nonneg (x * y + y * z + z * x - 3),
        hxyz, mul_self_nonneg (x * y * z - 1), 
        mul_self_nonneg (x - 1), mul_self_nonneg (y - 1), mul_self_nonneg (z - 1)]
    all_goals positivity
  linarith
  all_goals nlinarith