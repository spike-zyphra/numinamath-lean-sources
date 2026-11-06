import Mathlib

theorem algebra_10334 (a : ℝ) :
    (a^2 - 4) = 0 ↔ a = -2 ∨ a = 2 := by
  constructor
  · -- Assume denominator equals zero, prove a = -2 or a = 2
    intro h
    have h1 : a^2 - 4 = (a - 2) * (a + 2) := by ring
    rw [h1] at h
    cases (mul_eq_zero.1 h) with
    | inl h2 =>
      right
      linarith
    | inr h3 =>
      left
      linarith
  · -- Assume a = -2 or a = 2, prove denominator equals zero
    rintro (h | h)
    · -- Case where a = -2
      rw [h]
      norm_num
    · -- Case where a = 2
      rw [h]
      norm_num