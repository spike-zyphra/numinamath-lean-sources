import Mathlib

theorem algebra_222366 (x : ℝ) :
    x^4 + 5 * x^3 - 3 * x^2 - 35 * x - 28 = 0 ↔
    x = -1 ∨ x = -4 ∨ x = Real.sqrt 7 ∨ x = -Real.sqrt 7 := by
  constructor
  · -- Assume polynomial equals zero, prove the four roots
    intro h
    have h1 : (x + 1) * (x + 4) * (x^2 - 7) = 0 := by 
      ring_nf
      linarith

    cases' (mul_eq_zero.mp h1) with h2 h3
    cases' mul_eq_zero.mp h2 with h4 h5

    · -- Case x + 1 = 0, so x = -1
      left
      linarith

    · -- Case x + 4 = 0, so x = -4
      right
      left
      linarith

    · -- Case x^2 - 7 = 0, so x^2 = 7, hence x = ±√7

      have h6 : x^2 = 7 := by linarith

      have h7 : x = Real.sqrt 7 ∨ x = -Real.sqrt 7 := by 
        have h8 : x^2 = (7 : ℝ) := h6
        have h9 : x^2 - (7 : ℝ) = 0 := by linarith

        have h14 : (x - Real.sqrt 7) * (x + Real.sqrt 7) = 0 := by
          nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]

        cases' (mul_eq_zero.mp h14) with h15 h16

        · -- Case x - sqrt 7 = 0
          left
          linarith

        · -- Case x + sqrt 7 = 0
          right
          nlinarith [Real.sqrt_nonneg 7]

      cases h7 with
      | inl h8 =>
        -- Case x = Real.sqrt 7
        simp [h8]
        <;> nlinarith [Real.sqrt_nonneg 7]

      | inr h9 =>
        -- Case x = -Real.sqrt 7
        simp [h9]
        <;> nlinarith [Real.sqrt_nonneg 7]

  · -- Assume x is one of the four roots, prove the polynomial equals zero
    rintro (h | h | h | h)
    · -- Case x = -1
      rw [h]
      norm_num

    · -- Case x = -4
      rw [h]
      norm_num

    · -- Case x = Real.sqrt 7
      rw [h]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_nonneg (7 : ℝ)]

    · -- Case x = -Real.sqrt 7
      rw [h]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_nonneg (7 : ℝ)]