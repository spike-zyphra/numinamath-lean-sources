import Mathlib

theorem algebra_598934 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z * (x + y + z) = 1) :
    2 ≤ (x + y) * (y + z) := by
  have h1 : (x + y) * (y + z) = y * (x + y + z) + x * z := by
    ring
  have h2 : 0 < x * y * z * (x + y + z) := by 
    nlinarith [h]
  have h3 : 0 < x * y * z := by
    nlinarith [h, mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]
  have h4 : 0 < y * (x + y + z) := by
    nlinarith [h, mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]
  have h5 : x * z = 1 / (y * (x + y + z)) := by
    have h6 : y * (x + y + z) ≠ 0 := by
      nlinarith [show 0 < y * (x + y + z) by linarith [h4]]
    field_simp [h6]
    nlinarith [h]
  rw [h1]
  have h7 : y * (x + y + z) + x * z ≥ 2 := by
    rw [show x * z = 1 / (y * (x + y + z)) by linarith [h5]]
    have h8 : y * (x + y + z) + 1 / (y * (x + y + z)) ≥ 2 := by
      have h9 : 0 < y * (x + y + z) := by linarith [h4]
      have h10 : y * (x + y + z) + 1 / (y * (x + y + z)) - 2 ≥ 0 := by
        have h11 : y * (x + y + z) * (1 / (y * (x + y + z))) = 1 := by 
          field_simp [show y * (x + y + z) ≠ 0 by linarith [show 0 < y * (x + y + z) by linarith [h4]]]
        nlinarith [sq_nonneg (y * (x + y + z) - 1)]
      linarith [h10]
    linarith [h8]
  linarith [h7]