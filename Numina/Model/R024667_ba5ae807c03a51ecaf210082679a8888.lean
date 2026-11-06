import Mathlib

theorem algebra_323277 {m n : ℝ} (h : m^3 + n^3 + 3 * m * n = 1) : m + n = 1 ∨ m + n = -2 := by
  have h1 : (m + n - 1) * ((m + n)^2 + (m + n) + 1 - 3 * (m * n)) = 0 := by
    have h2 : m^3 + n^3 = (m + n) ^ 3 - 3 * (m * n) * (m + n) := by
      ring_nf
    have h3 : m^3 + n^3 + 3 * m * n = 1 := h
    rw [h2] at h3
    ring_nf at h3 ⊢
    nlinarith
  cases' (mul_eq_zero.mp h1) with h1' h2'
  · -- Case where m + n - 1 = 0
    left
    linarith
  · -- Case where (m + n)^2 + (m + n) + 1 - 3 * (m * n) = 0
    have h3 : (m + n)^2 + (m + n) + 1 = 3 * (m * n) := by
      linarith
    have h5 : (m + n) = -2 := by
      nlinarith [sq_nonneg (m - n), sq_nonneg (m + n + 2), sq_nonneg (m * n), sq_nonneg ((m + n) - (-2))]
    right
    linarith