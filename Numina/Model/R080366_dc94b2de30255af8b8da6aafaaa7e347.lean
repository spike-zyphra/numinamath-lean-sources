import Mathlib

theorem algebra_141718 (x : ℝ) :
    (x + 1998) * (x + 1999) * (x + 2000) * (x + 2001) + 1 = 0 ↔
    x = -3999 / 2 + 1 / 2 * Real.sqrt 5 ∨ x = -3999 / 2 - 1 / 2 * Real.sqrt 5 := by
  constructor
  · -- First direction: assume the equation holds, derive the two roots
    intro h
    have h1 : (x + 1998) * (x + 1999) * (x + 2000) * (x + 2001) + 1 = 0 := h
    have h2 : ((x + 1998) * (x + 1999) * (x + 2000) * (x + 2001) + 1) = ((x + 1998)^2 + 3 * (x + 1998) + 1) ^ 2 := by
      ring_nf
    rw [h2] at h1
    have h3 : (x + 1998)^2 + 3 * (x + 1998) + 1 = 0 := by
      apply pow_eq_zero
      exact h1
    have h5 : (x + 1998 + 3 / 2) ^ 2 = 5 / 4 := by
      nlinarith [h3, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    have h7 : x + 1998 + 3 / 2 = Real.sqrt 5 / 2 ∨ x + 1998 + 3 / 2 = -Real.sqrt 5 / 2 := by
      have h8 : (x + 1998 + 3 / 2 - Real.sqrt 5 / 2) * (x + 1998 + 3 / 2 + Real.sqrt 5 / 2) = 0 := by
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), h5, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      cases (mul_eq_zero.1 h8) with
      | inl h9 =>
        left
        linarith
      | inr h10 =>
        right
        linarith
    cases h7 with
    | inl h8 =>
      left
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    | inr h8 =>
      right
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  · -- Second direction: assume either of the two roots holds, prove the equation
    rintro (h | h)
    · -- First root
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    · -- Second root
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]