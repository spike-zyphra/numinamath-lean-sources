import Mathlib

theorem inequalities_193878 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x * y + y * z + z * x = 1) :
    5 / 2 ≤ 1 / (x + y) + 1 / (y + z) + 1 / (z + x) := by
  have h1 : x + y > 0 := by
    by_contra h2
    have h2 : x + y ≤ 0 := by linarith
    have hx0 : x = 0 := by nlinarith [show x ≥ 0 from hx, show y ≥ 0 from hy]
    have hy0 : y = 0 := by nlinarith [show x ≥ 0 from hx, show y ≥ 0 from hy]
    have h3 : x * y + y * z + z * x = 0 := by
      rw [hx0, hy0]
      nlinarith [show z ≥ 0 from hz]
    linarith [h, h3]
  have h2 : y + z > 0 := by
    by_contra h3
    have h3 : y + z ≤ 0 := by linarith
    have hy0 : y = 0 := by nlinarith [show y ≥ 0 from hy, show z ≥ 0 from hz]
    have hz0 : z = 0 := by nlinarith [show y ≥ 0 from hy, show z ≥ 0 from hz]
    have h4 : x * y + y * z + z * x = 0 := by
      rw [hy0, hz0]
      nlinarith [show x ≥ 0 from hx]
    linarith [h, h4]
  have h3 : z + x > 0 := by
    by_contra h4
    have h4 : z + x ≤ 0 := by linarith
    have hz0 : z = 0 := by nlinarith [show z ≥ 0 from hz, show x ≥ 0 from hx]
    have hx0 : x = 0 := by nlinarith [show z ≥ 0 from hz, show x ≥ 0 from hx]
    have h5 : x * y + y * z + z * x = 0 := by
      rw [hz0, hx0]
      nlinarith [show y ≥ 0 from hy]
    linarith [h, h5]
  have h4 : 1 / (x + y) + 1 / (y + z) + 1 / (z + x) - 5 / 2 ≥ 0 := by
    have pos1 : 0 < (x + y) * (y + z) * (z + x) := by positivity
    have h5 : 1 / (x + y) + 1 / (y + z) + 1 / (z + x) - 5 / 2 =
        ((y + z) * (z + x) + (x + y) * (z + x) + (x + y) * (y + z) - (5 / 2) * (x + y) * (y + z) * (z + x)) / ((x + y) * (y + z) * (z + x)) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y + z - 2), sq_nonneg (x * y + y * z + z * x - 1),
      mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx, h]
    positivity
  linarith