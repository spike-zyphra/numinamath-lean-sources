import Mathlib

theorem algebra_186667 (x : ℝ) (hx : (2*x-7)*(x+2)*(x-6) ≠ 0) :
    7*(x-2)*(x-3)*(x-4)/((2*x-7)*(x+2)*(x-6)) = -2 ↔
    x = 0 ∨ x = 5 ∨ x = 38/11 := by
  constructor
  · -- Assume the equation holds, prove the three solutions.
    intro h_eq
    have h1 : 7 * (x - 2) * (x - 3) * (x - 4) = -2 * ((2 * x - 7) * (x + 2) * (x - 6)) := by
      have h2 : (2 * x - 7) * (x + 2) * (x - 6) ≠ 0 := hx
      field_simp [h2] at h_eq ⊢
      linarith
    have h4 : 11 * x ^ 3 - 93 * x ^ 2 + 190 * x = 0 := by
      nlinarith [sq_nonneg (x - 0), sq_nonneg (x - 5), sq_nonneg (x - 38 / 11)]
    have h5 : x * (11 * x^2 - 93 * x + 190) = 0 := by
      ring_nf at h4 ⊢
      linarith
    cases' (mul_eq_zero.mp h5) with hx1 hx2
    · -- Case x = 0
      left
      linarith
    · -- Case 11 * x^2 - 93 * x + 190 = 0
      have h6 : 11 * x^2 - 93 * x + 190 = 0 := by
        nlinarith
      have h7 : (x - 5) * (x - 38 / 11) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- Case x = 5
        right
        left
        linarith
      · -- Case x = 38/11
        right
        right
        linarith
  · -- Assume the three solutions, prove the equation holds.
    rintro (h | h | h)
    · -- x = 0
      rw [h]
      norm_num
    · -- x = 5
      rw [h]
      norm_num
    · -- x = 38/11
      rw [h]
      norm_num