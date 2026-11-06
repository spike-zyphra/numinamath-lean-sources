import Mathlib

theorem algebra_165658 (x : ℝ) (hx : x^2 + 2 * x + 2 ≠ 0 ∧ x^2 + 2 * x + 3 ≠ 0) :
    (x^2 + 2 * x + 1) / (x^2 + 2 * x + 2) + (x^2 + 2 * x + 2) / (x^2 + 2 * x + 3) = 7 / 6 ↔
    x = 0 ∨ x = -2 := by
  constructor
  · -- Assume the equation holds, prove x = 0 or x = -2
    rintro h
    rcases hx with ⟨hx1, hx2⟩
    have h1 : (x ^ 2 + 2 * x + 2) ≠ 0 := hx1
    have h2 : (x ^ 2 + 2 * x + 3) ≠ 0 := hx2
    have h3 : (x ^ 2 + 2 * x + 2) ≠ 0 := h1
    have h4 : (x ^ 2 + 2 * x + 3) ≠ 0 := h2
    have eq1 : (x^2 + 2 * x + 1) / (x^2 + 2 * x + 2) + (x^2 + 2 * x + 2) / (x^2 + 2 * x + 3) = 7 / 6 := h
    have eq2 : 6 * (x + 1) ^ 2 * (x^2 + 2 * x + 3) + 6 * (x ^ 2 + 2 * x + 2) ^ 2 = 7 * (x ^ 2 + 2 * x + 2) * (x ^ 2 + 2 * x + 3) := by
      have h3 : (x^2 + 2 * x + 2) ≠ 0 := h1
      have h4 : (x^2 + 2 * x + 3) ≠ 0 := h2
      field_simp [h3, h4] at eq1 ⊢
      nlinarith [sq_pos_of_pos (show (0 : ℝ) < 3 by norm_num), sq_nonneg (x + 1), sq_nonneg (x ^ 2 + 2 * x + 2 - (x ^ 2 + 2 * x + 3)), sq_nonneg (x^2 + 2 * x + 2), sq_nonneg (x ^ 2 + 2 * x + 3)]
    have eq3 : 5 * (x^2 + 2 * x) ^ 2 + 13 * (x^2 + 2 * x) = 0 := by
      nlinarith [sq_nonneg (x ^ 2 + 2 * x + 2), sq_nonneg (x ^ 2 + 2 * x + 3), sq_nonneg (x * (x + 2)), sq_nonneg ((x + 1)), sq_nonneg ((x ^ 2 + 2 * x)), sq_nonneg (x^2 + 2*x - 2)]
    have eq4 : (x^2 + 2 * x) * (5 * (x^2 + 2 * x) + 13) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq4) with h5 h6
    · -- Case $x^2 + 2*x = 0$
      have h7 : x * (x + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- Case $x = 0$
        left
        linarith
      · -- Case $x + 2 = 0$ so $x = -2$
        right
        linarith
    · -- Case $5 * (x^2 + 2 * x) + 13 = 0$
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x^2 + 2 * x + 1), sq_nonneg ((x) ^ 2 + 2 * x - (-2 : ℝ)), sq_nonneg ((x) ^ 2 + 2 * x - (0 : ℝ)), sq_nonneg (x * (x + 2)), sq_pos_of_pos (show (0 : ℝ) < 3 by norm_num)]
  · -- Assume x = 0 or x = -2, prove the equation
    rintro (h | h)
    · -- Case x = 0
      rw [h]
      norm_num
    · -- Case x = -2
      rw [h]
      norm_num