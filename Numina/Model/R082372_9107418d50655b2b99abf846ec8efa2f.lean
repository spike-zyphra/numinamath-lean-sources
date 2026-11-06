import Mathlib

theorem algebra_232655 {a b c : ℝ} (h : a + b + c = 0) :
    a * b + a * c + b * c ≤ 0 := by
  have h1 : (a + b + c) ^ 2 = 0 := by
    rw [h]
    norm_num

  have h2 : a ^ 2 + b ^ 2 + c ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]

  have h3 : 2 * (a * b + a * c + b * c) = -(a ^ 2 + b ^ 2 + c ^ 2) := by
    have h4 : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + a * c + b * c) := by
      ring
    rw [h1] at h4
    linarith

  nlinarith [h2, h3]