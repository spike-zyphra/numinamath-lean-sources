import Mathlib

theorem algebra_15373 (x y z : ℝ) (hx : x ≠ y) (hy : y ≠ z) (hz : z ≠ x) (hsum : x + y + z = 0) :
    (x * y + y * z + z * x) / (x ^ 2 + y ^ 2 + z ^ 2) = -1 / 2 := by
  have h1 : x ^ 2 + y ^ 2 + z ^ 2 ≠ 0 := by
    by_contra h
    have h2 : x ^ 2 + y ^ 2 + z ^ 2 = 0 := by linarith
    have hx2 : x ^ 2 ≥ 0 := by apply sq_nonneg
    have hy2 : y ^ 2 ≥ 0 := by apply sq_nonneg
    have hz2 : z ^ 2 ≥ 0 := by apply sq_nonneg
    have hx0 : x ^ 2 = 0 := by
      linarith [h2, hx2, hy2, hz2]
    have hy0 : y ^ 2 = 0 := by
      linarith [h2, hx2, hy2, hz2]
    have hz0 : z ^ 2 = 0 := by
      linarith [h2, hx2, hy2, hz2]
    have hx0' : x = 0 := by
      nlinarith
    have hy0' : y = 0 := by
      nlinarith
    have hz0' : z = 0 := by
      nlinarith
    -- But this would mean x = y = z = 0, contradicting hx: x ≠ y
    exfalso
    exact hx (by
      linarith [hx0', hy0']
    )
  have h2 : x * y + y * z + z * x = -1 / 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    have h3 : (x + y + z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * (x * y + y * z + z * x) := by
      ring
    rw [hsum] at h3
    have h4 : 2 * (x * y + y * z + z * x) = - (x ^ 2 + y ^ 2 + z ^ 2 ) := by nlinarith
    linarith
  have h3 : (x * y + y * z + z * x) / (x ^ 2 + y ^ 2 + z ^ 2) = -1 / 2 := by
    have h4 : (x * y + y * z + z * x) = -1 / 2 * (x ^ 2 + y ^ 2 + z ^ 2) := h2
    have h5 : (x ^ 2 + y ^ 2 + z ^ 2) ≠ 0 := h1
    field_simp [h5]
    nlinarith
  exact h3