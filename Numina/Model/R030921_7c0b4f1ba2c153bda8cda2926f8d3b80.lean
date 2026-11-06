import Mathlib

theorem algebra_308384 (x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^3 - y^3 - z^3 = 3 * x * y * z) (h2 : x^2 = 2 * (y + z)) :
    x * y + y * z + z * x = 5 := by

  have h3 : (x - y - z) * (x^2 + y^2 + z^2 + x * y + x * z - y * z) = 0 := by
    nlinarith [sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x^2 - 2 * (y + z)), h1, h2]

  cases' (mul_eq_zero.mp h3) with h4 h5

  · -- Assume h4: x - y - z = 0.
    have h6 : x = y + z := by linarith

    rw [h6] at h2

    have h7 : (y + z) * (y + z - 2) = 0 := by
      nlinarith

    cases' (mul_eq_zero.mp h7) with h8 h9

    · -- Assume h8: y + z = 0.
      nlinarith

    · -- Assume h9: y + z - 2 = 0.
      have h10 : y + z = 2 := by linarith

      have hy1 : y = 1 := by
        nlinarith

      have hz1 : z = 1 := by
        nlinarith

      have hx2 : x = 2 := by 
        nlinarith

      rw [hx2, hy1, hz1]
      norm_num

  · -- Assume h5: x^2 + y^2 + z^2 + x * y + x * z - y * z = 0.
    nlinarith [sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]