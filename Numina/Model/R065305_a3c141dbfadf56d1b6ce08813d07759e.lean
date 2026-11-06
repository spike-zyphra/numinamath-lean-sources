import Mathlib

theorem algebra_68713 {x y : ℝ} (h1 : 3 * x + 4 * y = 26) (h2 : Real.sqrt (x ^ 2 + y ^ 2 - 4 * x + 2 * y + 5) +
    Real.sqrt (x ^ 2 + y ^ 2 - 20 * x - 10 * y + 125) = 10) :
    (x, y) = (6, 2) := by
  have h3 : x = (26 - 4 * y) / 3 := by
    linarith
  rw [h3] at h2
  have h4 : Real.sqrt (((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 4 * ((26 - 4 * y) / 3) + 2 * y + 5) ≥ 0 := by positivity
  have h5 : Real.sqrt (((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 20 * ((26 - 4 * y) / 3) - 10 * y + 125) ≥ 0 := by positivity
  have h6 : Real.sqrt (((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 4 * ((26 - 4 * y) / 3) + 2 * y + 5) = 10 - Real.sqrt (((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 20 * ((26 - 4 * y) / 3) - 10 * y + 125) := by linarith
  have h9 : (Real.sqrt (((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 4 * ((26 - 4 * y) / 3) + 2 * y + 5)) ^ 2 = (10 - Real.sqrt (((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 20 * ((26 - 4 * y) / 3) - 10 * y + 125)) ^ 2 := by
    rw [h6]
  have h10 : (Real.sqrt (((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 4 * ((26 - 4 * y) / 3) + 2 * y + 5)) ^ 2 = ((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 4 * ((26 - 4 * y) / 3) + 2 * y + 5 := by
    rw [Real.sq_sqrt]
    nlinarith
  have h11 : (10 - Real.sqrt (((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 20 * ((26 - 4 * y) / 3) - 10 * y + 125)) ^ 2 = 100 - 20 * Real.sqrt (((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 20 * ((26 - 4 * y) / 3) - 10 * y + 125) + (Real.sqrt (((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 20 * ((26 - 4 * y) / 3) - 10 * y + 125)) ^ 2 := by
    ring_nf
  rw [h10] at h9
  rw [h11] at h9
  have h12 : (Real.sqrt (((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 20 * ((26 - 4 * y) / 3) - 10 * y + 125)) ^ 2 = ((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 20 * ((26 - 4 * y) / 3) - 10 * y + 125 := by
    rw [Real.sq_sqrt]
    nlinarith
  rw [h12] at h9
  have hy : y = 2 := by
    nlinarith [Real.sqrt_nonneg (((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 4 * ((26 - 4 * y) / 3) + 2 * y + 5), Real.sqrt_nonneg (((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 20 * ((26 - 4 * y) / 3) - 10 * y + 125), Real.sq_sqrt (show ((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 4 * ((26 - 4 * y) / 3) + 2 * y + 5 ≥ 0 by nlinarith), Real.sq_sqrt (show ((26 - 4 * y) / 3) ^ 2 + y ^ 2 - 20 * ((26 - 4 * y) / 3) - 10 * y + 125 ≥ 0 by nlinarith)]
  have hx : x = 6 := by
    linarith [h1, hy]
  exact Prod.ext hx hy