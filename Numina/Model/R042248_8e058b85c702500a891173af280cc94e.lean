import Mathlib

theorem algebra_598945 (x y z r : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hr : 0 < r)
    (h1 : x^2 + y^2 = z^2) (h2 : x * y = r * z) :
    z * Real.sqrt (x^2 - r^2) = x^2 := by

  have h3 : y^2 = z^2 - x^2 := by
    nlinarith
  have h5 : x^4 + r^2 * z^2 = z^2 * x^2 := by
    have h6 : y = r * z / x := by
      have hne : x ≠ 0 := by nlinarith
      field_simp [hne]
      nlinarith [h2, hx.ne']
    rw [h6] at h1
    have h7 : x^4 + r^2 * z^2 = z^2 * x^2 := by
      field_simp [show x ≠ 0 by linarith] at h1 ⊢
      nlinarith [h1, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    nlinarith

  have h8 : x^2 ≥ r^2 := by
    nlinarith [sq_nonneg (x^2 - r^2), sq_nonneg (z - x), sq_nonneg (y * z - r * x), sq_nonneg (x * y - r * z), mul_pos hx hy, mul_pos hx hz, mul_pos hr hz, mul_pos hx hr]

  have h8' : x^2 - r^2 ≥ 0 := by
    linarith

  have h6'' : x^4 = z^2 * (x^2 - r^2) := by
    nlinarith [h5, sq_nonneg (x^2 - r^2)]

  have h7 : z * Real.sqrt (x^2 - r^2) = x^2 := by
    have h8'' : (Real.sqrt (x^2 - r^2)) ^2 = x^2 - r^2 := Real.sq_sqrt (by
      linarith
    )
    have h10 : (z * Real.sqrt (x^2 - r^2)) ^ 2 = x^4 := by
      calc
        (z * Real.sqrt (x^2 - r^2)) ^2
          = z^2 * (Real.sqrt (x^2 - r^2) ^2) := by ring
        _ = z^2 * (x^2 - r^2) := by
          rw [Real.sq_sqrt (by
            linarith
          )]
        _ = x^4 := by
          nlinarith [h6'']

    have h14 : (z * Real.sqrt (x^2 - r^2) - x^2) * (z * Real.sqrt (x^2 - r^2) + x^2) = 0 := by
      nlinarith [h10, sq_nonneg (x^2 - x^2), h6'']

    cases' (mul_eq_zero.1 h14) with h15 h16
    · -- Case for (A - B) = 0
      linarith
    · -- Case for positivity
      nlinarith [sq_nonneg (z * Real.sqrt (x^2 - r^2) - x^2), Real.sqrt_nonneg (x^2 - r^2), mul_pos hx hz, sq_nonneg (z - x), sq_nonneg (Real.sqrt (x^2 - r^2) - x/2), sq_nonneg (x - x), sq_nonneg (y - x), sq_nonneg (z - 2), Real.sqrt_nonneg (x^2 - r^2), Real.sq_sqrt (show x^2 - r^2 ≥ 0 by linarith)]
  exact h7