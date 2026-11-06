import Mathlib

theorem algebra_212426 {a b : ℝ} (ha : a ≠ b) (h1 : a + 9 = (b - 3) ^ 2) (h2 : b + 9 = (a - 3) ^ 2) :
    a ^ 2 + b ^ 2 = 35 := by
  have h3 : a + b = 5 := by
    have h4 : a - b = (b - 3) ^ 2 - (a - 3) ^ 2 := by linarith
    have h5 : (b - 3) ^ 2 - (a - 3) ^ 2 = (b - a) * (a + b - 6) := by
      ring
    rw [h5] at h4
    have h6 : b - a ≠ 0 := by
      intro h
      apply ha
      linarith
    have h7 : - (b - a) = (b - a) * (a + b - 6) := by linarith
    have h8 : -1 = a + b - 6 := by
      apply (mul_left_inj' h6).mp
      linarith
    linarith
  have h4 : a ^ 2 + b ^ 2 = 7 * (a + b) := by
    nlinarith
  rw [h3] at h4
  nlinarith