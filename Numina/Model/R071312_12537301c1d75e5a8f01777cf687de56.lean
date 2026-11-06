import Mathlib

theorem algebra_186578 (x : ℝ) (hx : x ≠ 4 ∧ x ≠ -3) :
    (x^2 + 1) / (x - 4) - (x^2 - 1) / (x + 3) = 23 ↔
    x = -55 / 16 ∨ x = 5 := by
  constructor
  · -- Forward direction: equation implies solutions
    intro h
    have h1 : x - 4 ≠ 0 := by
      intro h2
      apply hx.1
      linarith
    have h2 : x + 3 ≠ 0 := by
      intro h3
      apply hx.2
      linarith
    field_simp [h1, h2] at h
    have h3 : 16 * x^2 - 25 * x - 275 = 0 := by
      nlinarith
    have h4 : (x - 5) * (16 * x + 55) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case where x = 5
      right
      linarith
    · -- Case where 16x + 55 = 0
      left
      nlinarith
  · -- Backward direction: solutions imply equation
    rintro (h | h)
    · -- Case x = -55/16
      rw [h]
      norm_num
    · -- Case x = 5
      rw [h]
      norm_num