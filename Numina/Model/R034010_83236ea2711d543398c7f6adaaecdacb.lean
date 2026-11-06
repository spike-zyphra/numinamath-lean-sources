import Mathlib

theorem algebra_221423 (x : ℝ) (hx : x ≠ 0) : (4 * x + 18) / x = (12 * x - 58) / 2 ↔
    x = 6 ∨ x = -1 / 2 := by
  constructor
  · -- Assume (4 * x + 18) / x = (12 * x - 58) / 2, prove x = 6 ∨ x = -1 / 2
    intro h
    have eq1 : (4 * x + 18) / x = (12 * x - 58) / 2 := h
    have h1 : 2 * (4 * x + 18) = x * (12 * x - 58) := by
      have h2 : x ≠ 0 := hx
      have eq2 : (4 * x + 18) / x = (12 * x - 58) / 2 := h
      field_simp [h2] at eq2 ⊢
      nlinarith
    have h2 : 2 * x ^ 2 - 11 * x - 6 = 0 := by 
      nlinarith [h1]
    have : (x - 6) * (x + 1 / 2) = 0 := by
      nlinarith [h2]
    cases' (mul_eq_zero.1 this) with h3 h4
    · -- x - 6 = 0, so x = 6
      left
      linarith
    · -- x + 1/2 = 0, so x = -1/2
      right
      linarith
  · -- Assume x = 6 ∨ x = -1 / 2, prove (4 * x + 18) / x = (12 * x - 58) / 2
    rintro (h | h)
    · -- x = 6
      rw [h]
      norm_num
    · -- x = -1/2
      rw [h]
      norm_num