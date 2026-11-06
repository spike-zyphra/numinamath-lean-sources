import Mathlib

theorem inequalities_598404 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    1 / (1 + x + y) + 1 / (1 + y + z) + 1 / (1 + z + x) ≤ 1 := by
  have hx1 : 0 < 1 + x + y := by nlinarith
  have hy1 : 0 < 1 + y + z := by nlinarith
  have hz1 : 0 < 1 + z + x := by nlinarith
  have h1 : 1 / (1 + x + y) + 1 / (1 + y + z) + 1 / (1 + z + x) - 1 ≤ 0 := by
    have h2 : 0 < (1 + x + y) * (1 + y + z) * (1 + z + x) := by positivity
    have h3 : 1 / (1 + x + y) + 1 / (1 + y + z) + 1 / (1 + z + x) - 1 =
        ((1 + y + z) * (1 + z + x) + (1 + x + y) * (1 + z + x) + (1 + x + y) * (1 + y + z) - (1 + x + y) * (1 + y + z) * (1 + z + x)) / ((1 + x + y) * (1 + y + z) * (1 + z + x)) := by
      field_simp
      <;> ring
    rw [h3]
    apply div_nonpos_of_nonpos_of_nonneg
    nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
        sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
        hxyz, mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
    all_goals nlinarith
  linarith