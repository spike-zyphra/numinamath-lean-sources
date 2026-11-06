import Mathlib

theorem algebra_253651 :
    { x : ℝ | (x + 2) ^ 2 * (x + 5) * (x - 1) = 10 } =
    { -2 + Real.sqrt 10, -2 - Real.sqrt 10 } := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume (x + 2)^2 * (x + 5) * (x - 1) = 10, prove x = -2 + sqrt 10 or x = -2 - sqrt 10
    intro h
    have h1 : (x ^ 2 + 4 * x) ^ 2 - (x ^ 2 + 4 * x) - 30 = 0 := by
      nlinarith [h]
    have h2 : ((x ^ 2 + 4 * x) - 6) * ((x ^ 2 + 4 * x) + 5) = 0 := by
      nlinarith [h1]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case $x^2 + 4x - 6 = 0$
      have h5 : x ^ 2 + 4 * x - 6 = 0 := by
        linarith
      have h6 : (x - (-2 + Real.sqrt 10)) * (x - (-2 - Real.sqrt 10)) = 0 := by
        nlinarith [h5, Real.sqrt_pos.mpr (show 0 < (10 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num), sq_nonneg (x + 2), sq_nonneg (x + 2 - Real.sqrt 10)]
      cases' (mul_eq_zero.mp h6) with h7 h8
      · -- Case $x - (-2 + \sqrt{10}) = 0$
        left
        linarith
      · -- Case $x - (-2 - \sqrt{10}) = 0$
        right
        linarith
    · -- Case $x^2 + 4 x + 5 = 0$
      have h5 : x ^ 2 + 4 * x + 5 = 0 := by
        nlinarith
      nlinarith [sq_nonneg (x + 2)]
  · -- Assume x = -2 + sqrt 10 or x = -2 - sqrt 10, prove (x + 2)^2 * (x + 5) * (x - 1) = 10
    rintro (h | h)
    · -- Case x = -2 + Real.sqrt 10
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 10 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 10) (Real.sqrt_nonneg 10)]
    · -- Case x = -2 - Real.sqrt 10
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 10 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 10) (Real.sqrt_nonneg 10)]