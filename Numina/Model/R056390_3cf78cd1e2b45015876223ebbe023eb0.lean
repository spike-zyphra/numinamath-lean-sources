import Mathlib

theorem algebra_16835 (x : ℝ) :
    x^3 + (x + 1)^3 + (x + 2)^3 = (x + 3)^3 ↔ x = 3 := by
  constructor
  · -- Forward direction: equation implies x = 3
    intro h
    have h1 : x^3 + (x + 1)^3 + (x + 2)^3 - (x + 3)^3 = 0 := by
      linarith
    have h2 : x^3 + (x + 1)^3 + (x + 2)^3 - (x + 3)^3 = 2 * x^3 - 12 * x - 18 := by
      ring
    rw [h2] at h1
    have h3 : x^3 - 6 * x - 9 = 0 := by
      linarith
    have h4 : (x - 3) * (x^2 + 3 * x + 3) = 0 := by
      ring_nf at h3 ⊢
      linarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case x - 3 = 0, so x = 3
      linarith
    · -- Case x^2 + 3x + 3 = 0, show contradiction
      have h7 : x^2 + 3 * x + 3 > 0 := by
        nlinarith [sq_nonneg (x + 3 / 2)]
      nlinarith
  · -- Backward direction: x = 3 implies equation
    intro h
    rw [h]
    norm_num