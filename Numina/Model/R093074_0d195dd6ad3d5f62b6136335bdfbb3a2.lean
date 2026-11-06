import Mathlib

theorem algebra_246490 (x : ℝ) : (x + 1)^2 * (x - 4)^2 + 4 * (x^2 - 3 * x - 4) = 0 ↔ x = -1 ∨ x = 0 ∨ x = 3 ∨ x = 4 := by
  constructor
  · -- Forward direction: if the equation equals zero, then x is one of the roots
    intro h
    have h1 : (x + 1) * (x - 4) * x * (x - 3) = 0 := by
      ring_nf at h ⊢
      linarith
    cases' (mul_eq_zero.mp h1) with h2 h3
    · cases' (mul_eq_zero.mp h2) with h4 h5
      · cases' (mul_eq_zero.mp h4) with h6 h7
        · -- x + 1 = 0, so x = -1
          left
          linarith
        · -- x - 4 = 0, so x = 4
          right
          right
          right
          linarith
      · -- x = 0
        right
        left
        linarith
    · -- x - 3 = 0, so x = 3
      right
      right
      left
      linarith
  · -- Backward direction: if x is a root, then the equation equals zero
    rintro (h | h | h | h)
    · -- x = -1
      rw [h]
      norm_num
    · -- x = 0
      rw [h]
      norm_num
    · -- x = 3
      rw [h]
      norm_num
    · -- x = 4
      rw [h]
      norm_num