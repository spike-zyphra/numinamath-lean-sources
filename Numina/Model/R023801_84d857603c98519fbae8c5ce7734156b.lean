import Mathlib

theorem algebra_153211 (x : ℝ) (hx : x ≠ -1) :
    x^2 + (x / (x + 1))^2 = 3 ↔ x = (1 + Real.sqrt 5) / 2 ∨ x = (1 - Real.sqrt 5) / 2 := by
  constructor
  · -- Assume x^2 + (x / (x + 1))^2 = 3, prove x = (1 + Real.sqrt 5) / 2 ∨ x = (1 - Real.sqrt 5) / 2
    intro h_eq
    have h1 : x + 1 ≠ 0 := by
      intro h
      apply hx
      linarith
    have eq1 : x^2 + (x / (x + 1))^2 = 3 := h_eq
    have eq2 : x^2 * (x + 1)^2 + x^2 = 3 * (x + 1)^2 := by
      have h11 : x + 1 ≠ 0 := h1
      field_simp [h11] at eq1 ⊢
      nlinarith [sq_pos_of_ne_zero (show (x + 1 : ℝ) ≠ 0 by exact h11), sq_nonneg (x + 1)]
    have eq3 : (x ^ 2 - x - 1) * (x ^ 2 + 3 * x + 3) = 0 := by
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x ^ 2 * (x + 1) ^ 2),
                 sq_nonneg (x * (x + 1)), sq_nonneg (x ^ 2 - x - 1), sq_nonneg (x ^ 2 + 3 * x + 3),
                 sq_nonneg (x + 1/2)]
    cases' (mul_eq_zero.mp eq3) with eq4 eq5
    · -- Case $x^2 - x - 1 = 0$
      have h2 : x ^ 2 - x - 1 = 0 := eq4
      have h3 : (x - (1 + Real.sqrt 5) / 2) * (x - (1 - Real.sqrt 5) / 2) = 0 := by
        nlinarith [Real.sqrt_nonneg 5, Real.sqrt_pos.mpr (show (5:ℝ) > (0:ℝ) by norm_num), Real.sq_sqrt (show (0:ℝ) ≤ (5:ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h3) with h4 h5
      · -- Case $x = (1 + Real.sqrt 5) / 2$
        left
        linarith
      · -- Case $x = (1 - Real.sqrt 5) / 2$
        right
        linarith
    · -- Case $x^2 + 3 x + 3 = 0$
      have h4 : x ^ 2 + 3 * x + 3 = 0 := eq5
      nlinarith [sq_nonneg (x + 3 / 2)]
  · -- Assume x = (1 + Real.sqrt 5) / 2 ∨ x = (1 - Real.sqrt 5) / 2 prove x^2 + (x / (x + 1))^2 = 3
    rintro (h_eq | h_eq)
    · -- Case x = (1 + Real.sqrt 5) / 2
      have hx1 : x = (1 + Real.sqrt 5) / 2 := h_eq
      have h1 : x + 1 ≠ 0 := by
        intro h
        apply hx
        linarith
      have h2 : x ^ 2 = x + 1 := by
        nlinarith [Real.sqrt_nonneg 5, Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_nonneg (x - 1), sq_nonneg (x * Real.sqrt 5)]
      have hx2 : x / (x + 1) = ( -1 + Real.sqrt 5 ) / 2 := by
        rw [hx1]
        field_simp [(show (3 + Real.sqrt 5 : ℝ) ≠ 0 by
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
        ), (show (2 : ℝ) ≠ 0 by norm_num)]
        <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      rw [hx2]
      nlinarith [Real.sqrt_nonneg 5, Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), sq_nonneg (x * (x + 1)), sq_nonneg (x * Real.sqrt 5), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    · -- Case x = (1 - Real.sqrt 5) / 2
      have hx1 : x = (1 - Real.sqrt 5) / 2 := h_eq
      have h1 : x + 1 ≠ 0 := by
        intro h
        apply hx
        linarith
      have h2 : x ^ 2 = x + 1 := by
        nlinarith [Real.sqrt_nonneg 5, Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_nonneg (x - 1), sq_nonneg (x * Real.sqrt 5)]
      have hx2' : x / (x + 1) = (-1 - Real.sqrt 5) / 2 := by
        rw [show x = (1 - Real.sqrt 5) / 2 by linarith]
        have h7 : ( (1 - Real.sqrt 5 : ℝ) / 2 / ((1 - Real.sqrt 5 : ℝ) / 2 + 1 ) ) = (-1 - Real.sqrt 5) / 2 := by
          have h8 : ( (1 - Real.sqrt 5 : ℝ) / 2 + 1 ) = (3 - Real.sqrt 5) / 2 := by
            nlinarith
          rw [h8]
          field_simp [(show (3 - Real.sqrt 5 : ℝ) ≠ 0 by
            nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          ), (show (2 : ℝ) ≠ 0 by norm_num)]
          <;> ring_nf <;> norm_num
          <;> nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        linarith
      rw [hx2']
      nlinarith [Real.sqrt_nonneg 5, Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), sq_nonneg (x * (x + 1)), sq_nonneg ((-1 - Real.sqrt 5) / 2 * (x + 1)), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), hx1, h2, Real.sqrt_nonneg 5]