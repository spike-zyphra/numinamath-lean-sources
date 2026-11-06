import Mathlib

theorem algebra_101408 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z * (x + y + z) = 1) :
    (x + y) * (y + z) ≥ 2 := by
  have h1 : (x + y) * (y + z) = y * (x + y + z) + x * z := by
    ring
  rw [h1]
  have h2 : x * z > 0 := mul_pos hx hz
  have h3 : y * (x + y + z) = 1 / (x * z) := by
    have h2' : x * z ≠ 0 := by
      apply mul_ne_zero
      linarith [hx.ne.symm]
      linarith [hz.ne.symm]
    field_simp
    nlinarith [h, mul_pos (show 0 < x by linarith [hx]) (show 0 < z by linarith [hz]), mul_pos (show 0 < y by linarith [hy]) (show 0 < x by linarith [hx]), mul_pos (show 0 < y by linarith [hy]) (show 0 < z by linarith [hz])]
  have h4 : y * (x + y + z) + x * z ≥ 2 := by
    have h5 : y * (x + y + z) = 1 / (x * z) := h3
    rw [h5]
    have h6 : (1 / (x * z) + x * z) - 2 ≥ 0 := by
      have h7 : (1 / (x * z) + x * z - 2) ≥ 0 := by
        have h8 : x * z > 0 := h2
        have h9 : (1 / (x * z) + x * z - 2) = (x * z - 1)^2 / (x * z) := by
          field_simp [h8]
          ring
        have h10 : (x * z - 1)^2 ≥ 0 := by
          exact sq_nonneg (x * z - 1)
        have h11 : (x * z - 1)^2 / (x * z) ≥ 0 := by
          apply div_nonneg h10
          nlinarith [h2]
        linarith [h9, h11]
      linarith [h7]
    linarith [h6]
  linarith [h4]