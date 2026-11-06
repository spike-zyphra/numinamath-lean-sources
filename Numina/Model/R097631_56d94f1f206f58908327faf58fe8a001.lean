import Mathlib

theorem algebra_146927 (a b c d e : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0)
    (hd : d ≥ 0) (he : e ≥ 0) (h1 : a + b + c + d + e = 8) (h2 : a^2 + b^2 + c^2 + d^2 + e^2 = 16) :
    e ≤ 16 / 5 := by
  have h3 : a + b + c + d = 8 - e := by linarith
  have h4 : a^2 + b^2 + c^2 + d^2 = 16 - e^2 := by linarith
  have h5 : a^2 + b^2 + c^2 + d^2 ≥ (a + b + c + d) ^ 2 / 4 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
  rw [h3] at h5
  rw [h4] at h5
  nlinarith