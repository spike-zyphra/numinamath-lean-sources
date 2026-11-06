import Mathlib

theorem algebra_241668 (x y : ℝ) (hx : 4 * (x ^ 4 + 3 * x ^ 2 + 3) * (y ^ 4 - 7 * y ^ 2 + 14) = 21) :
    (x = 0 ∧ y = Real.sqrt (7 / 2)) ∨ (x = 0 ∧ y = -Real.sqrt (7 / 2)) := by
  have h1 : (x ^ 4 + 3 * x ^ 2 + 3) ≥ 3 := by
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x)]
  have h2 : (y ^ 4 - 7 * y ^ 2 + 14) ≥ 7 / 4 := by
    nlinarith [sq_nonneg (y ^ 2 - 7 / 2), sq_nonneg (y), sq_nonneg (y ^ 2 - 2)]
  have h3 : (x ^ 4 + 3 * x ^ 2 + 3) = 3 := by
    nlinarith [sq_nonneg (x ^ 2 - 0), sq_nonneg (y ^ 2 - 7 / 2), sq_nonneg (x), sq_nonneg (y ^ 2 - 2)]
  have h4 : x ^ 2 = 0 := by
    nlinarith [h3, sq_nonneg (x ^ 2), sq_nonneg (x)]
  have h5 : x = 0 := by
    nlinarith
  have h6 : (y ^ 4 - 7 * y ^ 2 + 14) = 7 / 4 := by
    nlinarith [sq_nonneg (x ^ 2 - 0), sq_nonneg (y ^ 2 - 7 / 2), sq_nonneg (x), sq_nonneg (y ^ 2 - 2)]
  have h7 : y ^ 2 = 7 / 2 := by
    nlinarith [sq_nonneg (y ^ 2 - 7 / 2), sq_nonneg (y), sq_nonneg (y ^ 2 - 2), h6]
  have h8 : y = Real.sqrt (7 / 2) ∨ y = -Real.sqrt (7 / 2) := by
    have h9 : y^2 = 7 / 2 := h7
    have h10 : y^2 -7/2 = 0 := by linarith
    have h11 : (y - Real.sqrt (7 / 2)) * (y + Real.sqrt (7 / 2)) = 0 := by
      nlinarith [Real.sqrt_nonneg (7 / 2), Real.sq_sqrt (show (0 : ℝ) ≤ (7 / 2 : ℝ) by linarith)]
    cases' (mul_eq_zero.1 h11) with h12 h13
    · left
      linarith
    · right
      linarith
  cases h8 with
  | inl hy1 =>
    left
    tauto
  | inr hy2 =>
    right
    tauto