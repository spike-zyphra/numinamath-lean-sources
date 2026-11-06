import Mathlib

theorem algebra_165572 (x : ℝ) : (x + 1)^2 * (x + 2) + (x - 1)^2 * (x - 2) = 12 ↔ x = 1 := by
  constructor
  · -- Forward direction: prove that if the equation holds, then x = 1.
    intro h
    have h1 : (x + 1)^2 * (x + 2) + (x - 1)^2 * (x - 2) - 12 = 0 := by linarith
    have h2 : x^3 + 5 * x - 6 = 0 := by 
      ring_nf at h1 ⊢
      linarith
    have h3 : (x - 1) * (x^2 + x + 6) = 0 := by
      ring_nf at h2 ⊢
      linarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case where x - 1 = 0, so x = 1
      linarith
    · -- Show that x^2 + x + 6 = 0 has no real solutions
      have h6 : x^2 + x + 6 > 0 := by
        nlinarith [sq_nonneg (x + 1 / 2)]
      linarith
  · -- Backward direction: prove that if x = 1, then the equation holds.
    intro h
    rw [h]
    norm_num