import Mathlib

theorem algebra_13205 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a + b + c = 0) (h2 : a^4 + b^4 + c^4 = 128) :
    a * b + b * c + c * a = -8 := by
  have h3 : a * b + b * c + c * a = - (a^2 + b^2 + c^2) / 2 := by
    have h31 : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by
      ring
    rw [h1] at h31
    linarith
  have h4 : (a^2 + b^2 + c^2)^2 = 128 + 2 * ( (a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2 ) := by
    calc
      (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 = a^4 + b^4 + c^4 + 2 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) := by ring
      _ = a^4 + b^4 + c^4 + 2 * ( (a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2 ) := by ring
      _ = 128 + 2 * ( (a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2 ) := by rw [h2]
  have h5 : (a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2 = (a * b + b * c + c * a) ^ 2 := by
    have h51 : (a * b + b * c + c * a) ^ 2 = (a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2 + 2 * (a * b * b * c + b * c * c * a + c * a * a * b) := by
      ring
    have h52 : a * b * b * c + b * c * c * a + c * a * a * b = a * b * c * (a + b + c) := by
      ring
    rw [h1] at h52
    rw [h52] at h51
    linarith
  have h6 : (a^2 + b^2 + c^2)^2 = 128 + 2 * (a * b + b * c + c * a) ^ 2 := by
    rw [h5] at h4
    linarith
  have h7 : (a^2 + b^2 + c^2)^2 = 128 + ( (a^2 + b^2 + c^2) ^ 2 ) / 2 := by
    have h71 : (a * b + b * c + c * a) ^ 2 = ( (a^2 + b^2 + c^2) ^ 2 ) / 4 := by
      rw [show a * b + b * c + c * a = - (a^2 + b^2 + c^2) / 2 by linarith [h3]]
      ring_nf
    rw [h71] at h6
    linarith
  have h8 : (a^2 + b^2 + c^2) ^ 2 = 256 := by
    nlinarith
  have h9 : a^2 + b^2 + c^2 ≥ 0 := by
    nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
  have h10 : a^2 + b^2 + c^2 = 16 := by
    nlinarith
  rw [h10] at h3
  linarith