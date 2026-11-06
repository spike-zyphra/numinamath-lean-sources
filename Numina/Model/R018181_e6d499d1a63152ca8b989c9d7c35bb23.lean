import Mathlib

theorem algebra_271010 (x y z : ℕ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : (x * y / z : ℚ) + (x * z / y : ℚ) + (y * z / x : ℚ) = 3) :
    (x, y, z) = (1, 1, 1) := by
  have eq1 : (x * y : ℚ) ^ 2 + (x * z : ℚ) ^ 2 + (y * z : ℚ) ^ 2 = 3 * (x * y * z : ℚ) := by
    have h2 : (x * y / z + x * z / y + y * z / x : ℚ) = 3 := h
    field_simp at h2 ⊢
    <;> nlinarith [sq_pos_of_pos (show (0 : ℚ) < x from by positivity), sq_pos_of_pos (show (0 : ℚ) < y from by positivity), sq_pos_of_pos (show (0 : ℚ) < z from by positivity), mul_pos (show (0 : ℚ) < x from by positivity) (show (0 : ℚ) < y from by positivity), mul_pos (show (0 : ℚ) < x from by positivity) (show (0 : ℚ) < z from by positivity), mul_pos (show (0 : ℚ) < y from by positivity) (show (0 : ℚ) < z from by positivity)]
  have eq2 : (x * y) ^ 2 + (x * z) ^ 2 + (y * z) ^ 2 = 3 * (x * y * z) := by
    exact_mod_cast eq1
  have h1 : x ≤ 3 := by
    nlinarith [sq_nonneg (x * y - x * z : ℤ), sq_nonneg (x * y - y * z : ℤ), sq_nonneg (x * z - y * z : ℤ), sq_nonneg ((x : ℤ) - 1), sq_nonneg ((y : ℤ) - 1), sq_nonneg ((z : ℤ) - 1), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  have h2 : y ≤ 3 := by
    nlinarith [sq_nonneg (x * y - x * z : ℤ), sq_nonneg (x * y - y * z : ℤ), sq_nonneg (x * z - y * z : ℤ), sq_nonneg ((y : ℤ) - 1), sq_nonneg ((z : ℤ) - 1), sq_nonneg ((x : ℤ) - 1), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  have h3 : z ≤ 3 := by
    nlinarith [sq_nonneg (x * y - x * z : ℤ), sq_nonneg (x * y - y * z : ℤ), sq_nonneg (x * z - y * z : ℤ), sq_nonneg ((z : ℤ) - 1), sq_nonneg ((x : ℤ) - 1), sq_nonneg ((y : ℤ) - 1), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  interval_cases x <;> interval_cases y <;> interval_cases z <;> norm_num [Prod.ext_iff] at eq2 ⊢
  <;> tauto