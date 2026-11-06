import Mathlib

theorem algebra_4602 {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
(h : (6*a - 1)*(3*b^2 - 11)*(2*b^2) = 1440) : b = 3 := by
  have h1 : b ≥ 2 := by
    by_contra h2
    push_neg at h2
    have : b = 1 := by
      omega
    rw [this] at h
    ring_nf at h
    omega
  have h2 : b ≤ 4 := by
    by_contra h2
    push_neg at h2
    have h3 : 2 * b ^ 2 ≥ 32 := by 
      nlinarith [h2, sq_nonneg b]
    have h4 : 3 * b ^ 2 - 11 ≥ 16 := by 
      nlinarith [h2, sq_nonneg b]
    have h5 : (6 * a - 1 : ℤ) * (3 * b ^ 2 - 11) ≥ 0 := by 
      nlinarith
    nlinarith [h, h3, h4, sq_nonneg (6 * a - 1 : ℤ), sq_nonneg (3 * b ^ 2 - 11 : ℤ)]
  have h3 : b = 2 ∨ b = 3 ∨ b = 4 := by 
    omega
  rcases h3 with (h4 | h5 | h6)
  · -- Assume b = 2.
    rw [show b = 2 by linarith] at h
    ring_nf at h
    omega
  · -- Assume b = 3.
    have : b = 3 := by linarith
    assumption
  · -- Assume b = 4.
    rw [show b = 4 by linarith] at h
    ring_nf at h
    omega