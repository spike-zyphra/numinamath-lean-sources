import Mathlib

theorem algebra_304335 (a : ℝ) (ha : 0 ≤ a) (x : ℝ) :
    x^4 + 6 * x^3 + (9 - 2 * a) * x^2 - 6 * a * x + a^2 - 4 = 0 ↔
    x = (-3 + Real.sqrt (4 * a + 1)) / 2 ∨ x = (-3 - Real.sqrt (4 * a + 1)) / 2 ∨
    x = (-3 + Real.sqrt (4 * a + 17)) / 2 ∨ x = (-3 - Real.sqrt (4 * a + 17)) / 2 := by
  constructor
  · -- Forward direction: prove root implies factor
    intro h
    have h1 : (x ^ 2 + 3 * x + (2 - a)) * (x ^ 2 + 3 * x - (2 + a)) = 0 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x * 3), sq_nonneg (x - 2), sq_nonneg (x * a - a), sq_nonneg (x * a - 2), sq_nonneg (x + 3)]
    cases' (mul_eq_zero.mp h1) with h2 h3
    · -- First quadratic factor equals zero
      have h4 : x ^ 2 + 3 * x + (2 - a) = 0 := h2
      have h5 : (x - (-3 + Real.sqrt (4 * a + 1)) / 2) * (x - (-3 - Real.sqrt (4 * a + 1)) / 2) = 0 := by
        nlinarith [Real.sqrt_nonneg (4 * a + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * a + 1 by linarith [ha]), sq_nonneg (x - (-3 + Real.sqrt (4 * a + 1)) / 2), sq_nonneg (x - (-3 - Real.sqrt (4 * a + 1)) / 2)]
      cases' (mul_eq_zero.mp h5) with h6 h7
      · -- First root
        left
        linarith
      · -- Second root
        right
        left
        linarith
    · -- Second quadratic factor equals zero
      have h8 : x ^ 2 + 3 * x - (2 + a) = 0 := h3
      have h9 : (x - (-3 + Real.sqrt (4 * a + 17)) / 2) * (x - (-3 - Real.sqrt (4 * a + 17)) / 2) = 0 := by
        nlinarith [Real.sqrt_nonneg (4 * a + 17), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * a + 17 by linarith [ha]), sq_nonneg (x - (-3 + Real.sqrt (4 * a + 17)) / 2), sq_nonneg (x - (-3 - Real.sqrt (4 * a + 17)) / 2)]
      cases' (mul_eq_zero.mp h9) with h10 h11
      · -- Third root
        right
        right
        left
        linarith
      · -- Fourth root
        right
        right
        right
        linarith
  · -- Backward direction: prove factor implies root
    rintro (h | h | h | h)
    · -- First root
      rw [h]
      nlinarith [Real.sqrt_nonneg (4 * a + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * a + 1 by linarith [ha]), sq_nonneg (Real.sqrt (4 * a + 1)), sq_nonneg (Real.sqrt (4 * a + 17)), Real.sqrt_nonneg (4 * a + 17), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * a + 17 by linarith [ha]), sq_nonneg (-3 + Real.sqrt (4 * a + 1)), sq_nonneg (-3 - Real.sqrt (4 * a + 1)), sq_nonneg (-3 + Real.sqrt (4 * a + 17)), sq_nonneg (-3 - Real.sqrt (4 * a + 17)), sq_nonneg (a)]
    · -- Second root
      rw [h]
      nlinarith [Real.sqrt_nonneg (4 * a + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * a + 1 by linarith [ha]), sq_nonneg (Real.sqrt (4 * a + 1)), sq_nonneg (Real.sqrt (4 * a + 17)), Real.sqrt_nonneg (4 * a + 17), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * a + 17 by linarith [ha]), sq_nonneg (-3 + Real.sqrt (4 * a + 1)), sq_nonneg (-3 - Real.sqrt (4 * a + 1)), sq_nonneg (-3 + Real.sqrt (4 * a + 17)), sq_nonneg (-3 - Real.sqrt (4 * a + 17)), sq_nonneg (a)]
    · -- Third root
      rw [h]
      nlinarith [Real.sqrt_nonneg (4 * a + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * a + 1 by linarith [ha]), sq_nonneg (Real.sqrt (4 * a + 1)), sq_nonneg (Real.sqrt (4 * a + 17)), Real.sqrt_nonneg (4 * a + 17), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * a + 17 by linarith [ha]), sq_nonneg (-3 + Real.sqrt (4 * a + 1)), sq_nonneg (-3 - Real.sqrt (4 * a + 1)), sq_nonneg (-3 + Real.sqrt (4 * a + 17)), sq_nonneg (-3 - Real.sqrt (4 * a + 17)), sq_nonneg (a)]
    · -- Fourth root
      rw [h]
      nlinarith [Real.sqrt_nonneg (4 * a + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * a + 1 by linarith [ha]), sq_nonneg (Real.sqrt (4 * a + 1)), sq_nonneg (Real.sqrt (4 * a + 17)), Real.sqrt_nonneg (4 * a + 17), Real.sq_sqrt (show (0 : ℝ) ≤ 4 * a + 17 by linarith [ha]), sq_nonneg (-3 + Real.sqrt (4 * a + 1)), sq_nonneg (-3 - Real.sqrt (4 * a + 1)), sq_nonneg (-3 + Real.sqrt (4 * a + 17)), sq_nonneg (-3 - Real.sqrt (4 * a + 17)), sq_nonneg (a)]