import Mathlib

theorem algebra_192170 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 27) (hdiff : x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x = 0) :
    x = 9 ∧ y = 9 ∧ z = 9 := by
  have h1 : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 = 0 := by
    nlinarith
  have h2 : (x - y) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h3 : (y - z) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h4 : (z - x) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h5 : x - y = 0 := by
    rwa [sq_eq_zero_iff] at h2
  have h6 : y - z = 0 := by
    rwa [sq_eq_zero_iff] at h3
  have h7 : x = y := by linarith
  have h8 : y = z := by linarith
  have hx9 : x = 9 := by
    have h_eq : x = y := h7
    have h_eq2 : y = z := h8
    have hsum2 : x + y + z = 27 := hsum
    rw [h_eq, h_eq2] at hsum2
    linarith
  have hy9 : y = 9 := by linarith [h7, hx9]
  have hz9 : z = 9 := by linarith [h8, hy9]
  exact ⟨hx9, hy9, hz9⟩