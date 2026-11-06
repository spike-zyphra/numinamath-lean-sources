import Mathlib

theorem algebra_6766 {a b : ℝ} (ha : a^2 + b^2 = 100) (hb : 0 ≤ 100 - 2 * a) (hc : 0 ≤ 2 * a - 10 * b + 200) (hd : Real.sqrt (100 - 2 * a) + Real.sqrt (2 * a - 10 * b + 200) = 20) :
    (a = 0 ∧ b = 10) ∨ (a = 0 ∧ b = -10) := by

  have h1 : (Real.sqrt (100 - 2 * a)) ^ 2 = 100 - 2 * a := Real.sq_sqrt hb
  have h2 : (Real.sqrt (2 * a - 10 * b + 200)) ^ 2 = 2 * a - 10 * b + 200 := Real.sq_sqrt hc
  have h3 : Real.sqrt (100 - 2 * a) + Real.sqrt (2 * a - 10 * b + 200) = 20 := hd

  have h6 : a = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (100 - 2 * a) - 10), sq_nonneg (Real.sqrt (2 * a - 10 * b + 200) - 10), Real.sqrt_nonneg (100 - 2 * a), Real.sqrt_nonneg (2 * a - 10 * b + 200)]

  have h7 : b ^ 2 = 100 := by
    rw [h6] at ha
    nlinarith

  have h8 : b = 10 ∨ b = -10 := by
    have h : b ^ 2 = 100 := h7
    have : (b - 10) * (b + 10) = 0 := by nlinarith
    cases' (mul_eq_zero.1 this) with hb1 hb2
    · left
      linarith
    · right
      linarith

  cases h8 with
  | inl hb10 =>
    left
    constructor
    · linarith
    · linarith
  | inr hb10 =>
    right
    constructor
    · linarith
    · linarith