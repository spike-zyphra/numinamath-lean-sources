import Mathlib

theorem algebra_1155 {a b : ℝ} (h1 : a + b = 4) (h2 : a^2 + b^2 = 12) :
    a^5 + b^5 = 464 := by
  have h3 : a * b = 2 := by
    have h4 : a^2 + b^2 = (a + b) ^ 2 - 2 * (a * b) := by
      ring
    rw [h1] at h4
    nlinarith

  have h5 : a^3 + b^3 = 40 := by
    have h6 : a^3 + b^3 = (a + b) * (a^2 + b^2) - (a * b) * (a + b) := by
      ring
    rw [h1, h2, h3] at h6
    linarith

  have h7 : a^4 + b^4 = 136 := by
    have h8 : a^4 + b^4 = (a + b) * (a^3 + b^3) - (a * b) * (a^2 + b^2) := by
      ring
    rw [h1, h5, h2, h3] at h8
    linarith

  have h9 : a^5 + b^5 = (a + b) * (a^4 + b^4) - (a * b) * (a^3 + b^3) := by
    ring
  rw [h1, h7, h3, h5] at h9
  linarith