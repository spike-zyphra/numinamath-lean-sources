import Mathlib

theorem algebra_289525 (x : ℝ) (hx : x ≠ 0) : 1 / x + x / 80 = 7 / 30 ↔ x = 12 ∨ x = 20 / 3 := by 
  constructor
  · -- (→) If the equation holds, prove x = 12 or x = 20/3
    intro h_eq
    have h1 : x ≠ 0 := hx
    field_simp at h_eq
    have h2 : 3 * x ^ 2 - 56 * x + 240 = 0 := by 
      nlinarith
    have h3 : (x - 12) * (3 * x - 20) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- case where x = 12
      left
      linarith
    · -- case where 3x -20 =0 so x = 20/3
      right
      linarith
  · -- (←) If x = 12 or x = 20/3, prove the equation
    rintro (h_eq | h_eq)
    · -- x = 12
      rw [h_eq]
      norm_num
    · -- x = 20/3
      rw [h_eq]
      norm_num