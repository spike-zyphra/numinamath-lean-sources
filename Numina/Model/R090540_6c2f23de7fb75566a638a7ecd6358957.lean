import Mathlib

theorem algebra_188169 (x : ℝ) (hx : 3 * x ^ 2 + 5 * x - 14 ≠ 0 ∧ 3 * x ^ 2 + 5 * x - 10 ≠ 0) :
    (x ^ 2 + x + 2) / (3 * x ^ 2 + 5 * x - 14) = (x ^ 2 + x + 6) / (3 * x ^ 2 + 5 * x - 10) ↔
    x = 2 ∨ x = -4 := by 
  constructor
  · -- First implication: if the equation holds, then x = 2 or x = -4
    intro h
    have h1 : 3 * x ^ 2 + 5 * x - 14 ≠ 0 := hx.1
    have h2 : 3 * x ^ 2 + 5 * x - 10 ≠ 0 := hx.2
    field_simp [h1, h2] at h
    ring_nf at h
    have h3 : x^2 + 2 * x - 8 = 0 := by nlinarith
    have h4 : (x - 2) * (x + 4) = 0 := by
      nlinarith [h3]
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- Case where x - 2 = 0, so x = 2
      left
      linarith
    · -- Case where x + 4 = 0, so x = -4
      right
      linarith
  · -- Second implication: if x = 2 or x = -4, then the equation holds
    rintro (h | h)
    · -- Case x = 2
      rw [h]
      norm_num
    · -- Case x = -4
      rw [h]
      norm_num