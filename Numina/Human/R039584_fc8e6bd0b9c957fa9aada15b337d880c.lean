import Mathlib
/-solve the equation
x^4 + 2 * x^3 + 3 * x^2 + 2 * x - 81600
-/
theorem algebra_221020 (x : ℝ) :
    x^4 + 2 * x^3 + 3 * x^2 + 2 * x - 81600 = 0 ↔
    x = -1 / 2 + Real.sqrt (Real.sqrt 81601 - 3 / 4) ∨
    x = -1 / 2 - Real.sqrt (Real.sqrt 81601 - 3 / 4) := by
  constructor
  · -- Assume x^4 + 2 * x^3 + 3 * x^2 + 2 * x - 81600 = 0, we need to prove x is one of the two values
    intro h
    -- factorize --
    have h1 : (x ^ 2 + x + 1) ^ 2 = 81601 := by
      ring_nf at h ⊢
      nlinarith
    -- decrease the degree --
    have h3 : x ^ 2 + x + 1 = Real.sqrt 81601 := by
      have h5 : x ^ 2 + x + 1 > 0 := by
        have h1 : x ^ 2 + x + 1 = (x + 1 / 2) ^ 2 + 3 / 4 := by ring
        rw [h1]
        have h2 : (x + 1 / 2) ^ 2 ≥ 0 := sq_nonneg (x + 1 / 2)
        linarith
      have h6 : 0 ≤ Real.sqrt 81601 := Real.sqrt_nonneg 81601
      have h7 : (Real.sqrt 81601) ^ 2 = 81601 := Real.sq_sqrt (by norm_num)
      have h9 : (x ^ 2 + x + 1) ^ 2 - (Real.sqrt 81601) ^ 2 = 0 := by
          rw [h1, h7]
          ring
      have h10 : (x ^ 2 + x + 1 - Real.sqrt 81601) * (x ^ 2 + x + 1 + Real.sqrt 81601) = 0 := by
          linarith [h9]
      cases' (mul_eq_zero.mp h10) with h11 h12
      · -- x^2 + x + 1 - Real.sqrt 81601 = 0
        linarith
      · -- x^2 + x + 1 + Real.sqrt 81601 = 0
        have h13 : Real.sqrt 81601 ≥ 0 := Real.sqrt_nonneg 81601
        nlinarith [h5, h13]
    have h4 : (x + 1 / 2) ^ 2 = Real.sqrt 81601 - 3 / 4 := by
      nlinarith [sq_nonneg (x + 1 / 2), Real.sqrt_pos.mpr (by norm_num : (81601 : ℝ) > 0), h3]
    -- before remove the square, we have to show the right side is nonnegtive --
    have h5 : Real.sqrt 81601 - 3 / 4 ≥ 0 := by
      have h5 : Real.sqrt 81601 ≥ Real.sqrt 729 := Real.sqrt_le_sqrt (by norm_num)
      have h6 : Real.sqrt 729 = 27 := by
        rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
      linarith [h5, h6]
    have h6 : (x + 1 / 2) = Real.sqrt (Real.sqrt 81601 - 3 / 4) ∨ (x + 1 / 2) = -Real.sqrt (Real.sqrt 81601 - 3 / 4) := by
      have h7 : (x + 1 / 2) ^ 2 - (Real.sqrt (Real.sqrt 81601 - 3 / 4)) ^ 2 = 0 := by
        rw [h4]
        rw [Real.sq_sqrt (by linarith [h5])]
        ring
      have h8 : ((x + 1 / 2) - Real.sqrt (Real.sqrt 81601 - 3 / 4)) * ((x + 1 / 2) + Real.sqrt (Real.sqrt 81601 - 3 / 4)) = 0 := by
        linarith [h7]
      cases' (mul_eq_zero.mp h8) with h9 h10
      · -- (x + 1 / 2) - Real.sqrt (Real.sqrt 81601 - 3 / 4) = 0
        left
        linarith
      · -- (x + 1 / 2) + Real.sqrt (Real.sqrt 81601 - 3 / 4) = 0
        right
        linarith
    cases' h6 with h7 h8
    · -- (x + 1 / 2) = Real.sqrt (Real.sqrt 81601 - 3 / 4)
      left
      linarith
    · -- (x + 1 / 2) = -Real.sqrt (Real.sqrt 81601 - 3 / 4)
      right
      linarith

  · -- Assume x is one of the two values, we need to prove x^4 + 2 * x^3 + 3 * x^2 + 2 * x - 81600 = 0
    rintro (h | h)
    · -- x = -1/2 + sqrt(sqrt(81601) - 3/4)
      have h1 : x + 1 / 2 = Real.sqrt (Real.sqrt 81601 - 3 / 4) := by
        linarith [h]
      have h2 : (x + 1 / 2) ^ 2 = Real.sqrt 81601 - 3 / 4 := by
        have h2 : (Real.sqrt (Real.sqrt 81601 - 3 / 4)) ^ 2 = Real.sqrt 81601 - 3 / 4 := by
          rw [Real.sq_sqrt]
          have h3 : Real.sqrt 81601 - 3 / 4 ≥ 0 := by
            have h4 : Real.sqrt 81601 ≥ Real.sqrt 729 := Real.sqrt_le_sqrt (by norm_num)
            have h5 : Real.sqrt 729 = 27 := by
              rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
            linarith [h4, h5]
          linarith
        rw [h1]
        linarith
      have h3 : (x ^ 2 + x + 1) ^ 2 = 81601 := by
        have h5 : (x ^ 2 + x + 1) = Real.sqrt 81601 := by
          have h6 : (x + 1 / 2) ^ 2 + 3 / 4 = Real.sqrt 81601 := by
            linarith [h2]
          nlinarith [sq_nonneg (x + 1 / 2), Real.sqrt_pos.mpr (by norm_num : (81601 : ℝ) > 0)]
        rw [h5]
        have h7 : (Real.sqrt 81601) ^ 2 = 81601 := Real.sq_sqrt (by norm_num)
        linarith
      ring_nf at h3 ⊢
      nlinarith [sq_nonneg (x ^ 2 + x + 1), sq_nonneg (x ^ 2 + x + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 81601 by norm_num)]
    · -- x = -1/2 - sqrt(sqrt(81601) - 3/4)
      have h1 : x + 1 / 2 = -Real.sqrt (Real.sqrt 81601 - 3 / 4) := by
        linarith [h]
      have h2 : (x + 1 / 2) ^ 2 = Real.sqrt 81601 - 3 / 4 := by
        have h2 : (Real.sqrt (Real.sqrt 81601 - 3 / 4)) ^ 2 = Real.sqrt 81601 - 3 / 4 := by
          rw [Real.sq_sqrt]
          have h3 : Real.sqrt 81601 - 3 / 4 ≥ 0 := by
            have h4 : Real.sqrt 81601 ≥ Real.sqrt 729 := Real.sqrt_le_sqrt (by norm_num)
            have h5 : Real.sqrt 729 = 27 := by
              rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
            linarith [h4, h5]
          linarith
        rw [h1]
        nlinarith [Real.sqrt_nonneg (Real.sqrt 81601 - 3 / 4), h2]
      have h3 : (x ^ 2 + x + 1) ^ 2 = 81601 := by
        have h4 : (x + 1 / 2) ^ 2 = Real.sqrt 81601 - 3 / 4 := h2
        have h5 : (x ^ 2 + x + 1) = Real.sqrt 81601 := by
          have h6 : (x + 1 / 2) ^ 2 + 3 / 4 = Real.sqrt 81601 := by
            linarith [h4]
          nlinarith [sq_nonneg (x + 1 / 2), Real.sqrt_pos.mpr (by norm_num : (81601 : ℝ) > 0)]
        rw [h5]
        have h7 : (Real.sqrt 81601) ^ 2 = 81601 := Real.sq_sqrt (by norm_num)
        linarith
      ring_nf at h3 ⊢
      nlinarith [sq_nonneg (x ^ 2 + x + 1), sq_nonneg (x ^ 2 + x + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 81601 by norm_num)]