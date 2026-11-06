import Mathlib
theorem algebra_142615 {x y z : ℝ} (h1 : (x + 1) * y * z = 12) (h2 : (y + 1) * z * x = 4) (h3 : (z + 1) * x * y = 4) :
    (x, y, z) = (2, -2, -2) ∨ (x, y, z) = (1 / 3, 3, 3) := by
  have eq1 : x * (z - y) = 0 := by
    nlinarith [h1, h2, h3, sq_nonneg (x * (y - z)), sq_nonneg (y - z), sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
  cases' (mul_eq_zero.mp eq1) with h4 h5 
  · -- Case x = 0
    have hx0 : x = 0 := h4
    rw [hx0] at h2 h3
    nlinarith
  · -- Case y = z
    have hy_eq_z : z = y := by
      linarith
    rw [show z = y by linarith] at h1 h2 h3
    have eq2 : (x + 1) * y ^ 2 = 12 := by
      nlinarith
    have eq3 : y * (y + 1) * x = 4 := by
      ring_nf at h2 ⊢
      linarith
    have eq4 : y ^ 3 + y ^ 2 - 8 * y - 12 = 0 := by
      nlinarith [sq_nonneg (x), sq_nonneg (y - (-2)), sq_nonneg (y - 3), sq_nonneg (x - 2), sq_nonneg (x - 1 / 3)]
    have eq5 : (y + 2) ^ 2 * (y - 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq5) with eq6 eq7
    · -- Case y = -2
      have hy_eq1 : y = -2 := by
        nlinarith [pow_eq_zero (show (y + 2) ^ 2 = 0 by nlinarith)]
      have hx2 : x = 2 := by
        rw [hy_eq1] at eq3
        nlinarith
      have hz_eq : z = -2 := by
        nlinarith [hy_eq1, hy_eq_z]
      left
      simp [hx2, hy_eq1, hz_eq]
    · -- Case y = 3
      have hy_eq3 : y = 3 := by
        linarith
      have hx2 : x = 1 / 3 := by
        rw [hy_eq3] at eq3
        nlinarith
      have hz_eq3 : z = 3 := by
        nlinarith [hy_eq3, hy_eq_z]
      right
      simp [hx2, hy_eq3, hz_eq3]