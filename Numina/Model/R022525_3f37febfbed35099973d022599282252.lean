import Mathlib

theorem algebra_67092 {x : ℝ} : (x^2 + x - 2)^3 + (2 * x^2 - x - 1)^3 = 27 * (x^2 - 1)^3 ↔
    x = 1 ∨ x = -1 ∨ x = -2 ∨ x = -1 / 2 := by
  constructor
  · -- Assume the equation holds, prove the set of solutions
    intro h
    have h1 : (x^2 + x - 2)^3 + (2 * x^2 - x - 1)^3 - 27 * (x^2 - 1)^3 = 0 := by linarith
    have h2 : (x - 1) ^ 3 * ((x + 2) ^ 3 + (2 * x + 1) ^ 3 - 27 * (x + 1) ^ 3) = 0 := by
      ring_nf at h1 ⊢
      nlinarith
    cases (mul_eq_zero.1 h2) with
    | inl h3 =>
      have h4 : x - 1 = 0 := by
        have h5 : (x - 1) ^ 3 = 0 := by
          nlinarith
        have h6 : (x - 1) = 0 := by
          have h7 : (x - 1) ^ 3 = 0 := by linarith
          simp at h7 ⊢
          <;> nlinarith [h7]
        linarith
      left
      linarith
    | inr h3 =>
      have h3' : (x + 2) ^ 3 + (2 * x + 1) ^ 3 - 27 * (x + 1) ^ 3 = 0 := by
        nlinarith
      have h4 : (x + 1) * (2 * x + 1) * (x + 2) = 0 := by
        nlinarith [sq_nonneg (x + 2), sq_nonneg (2 * x + 1), sq_nonneg (x + 1)]
      cases' (mul_eq_zero.1 h4) with h5 h6
      cases' (mul_eq_zero.1 h5) with h7 h8
      · -- case where x + 1 = 0
        have h9 : x = -1 := by linarith
        right
        left
        linarith
      · -- case where 2x + 1 = 0
        have h10 : x = -1 / 2 := by linarith
        right
        right
        right
        linarith
      · -- case where x + 2 = 0
        have h11 : x = -2 := by linarith
        right
        right
        left
        linarith
  · -- Assume the set of solutions, prove the equation
    rintro (h | h | h | h)
    · -- x = 1
      rw [h]
      norm_num
    · -- x = -1
      rw [h]
      norm_num
    · -- x = -2
      rw [h]
      norm_num
    · -- x = -1/2
      rw [h]
      norm_num