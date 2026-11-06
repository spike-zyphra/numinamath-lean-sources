import Mathlib

open Real

/- 849. Compute the triple integral $I=\int_{-1}^{1} d x \int_{x^{2}}^{1} d y \int_{0}^{z}(4+z) d z$ and sketch its region of integration. -/
theorem calculus_185863 : ∫ x in (-1)..1, ∫ _y in (x^2)..1, ∫ z in (0)..2, (4 + z) = 40 / 3 := by
  -- Compute the inner integral.
  have eq3 : ∫ z in (0)..2, (4 + z) = 10 := by
    -- We have ∫ z in 0..2, (4 + z) = (∫ z in 0..2, 4) + ∫ z in 0..2, z = 2 * 4 + (2^2 - 0^2) / 2 = 10.
    rw [intervalIntegral.integral_add intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    rw [intervalIntegral.integral_const, integral_id]
    norm_num
  simp_rw [eq3]
  -- Compute the second inner integral.
  have eq2 x : ∫ y in (x^2)..1, 10 = 10 * (1 - x^2) := by
    -- We have ∫ y in x^2..1, 10 = (1 - x^2) * 10.
    simp [intervalIntegral.integral_const, mul_comm]
  simp_rw [eq2]
  -- ∫ x in (-1)..1, 10 * (1 - x^2) = 10 * ((∫ x in (-1)..1, 1) - ∫ x in (-1)..1, x^2)
  --    = 10 * ((1 - (-1)) * 1 - (1^3 - (-1)^3) / 3
  --    = 40 / 3.
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub intervalIntegrable_const (intervalIntegral.intervalIntegrable_pow 2)]
  rw [intervalIntegral.integral_const, integral_pow]
  norm_num