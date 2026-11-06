import Mathlib

theorem algebra_603443 (x y : ℝ) (h : x + y = 1) :
    (x^3 + 1) * (y^3 + 1) ≤ 4 ∧ ∃ x y : ℝ, x + y = 1 ∧ (x^3 + 1) * (y^3 + 1) = 4 := by
  constructor
  · -- First part: prove (x^3 + 1) * (y^3 + 1) ≤ 4
    have h1 : y = 1 - x := by
      linarith
    rw [h1]
    nlinarith [sq_nonneg ((1 - x) ^ 2 - x ^ 2), sq_nonneg ((1 - x) - x), sq_nonneg ((1 - x) ^ 2 + x ^ 2 - 1),
      sq_nonneg (x ^ 2 - 1), sq_nonneg ((1 - x) ^ 2 - 1), mul_self_nonneg (x ^ 2 - 1),
      mul_self_nonneg ((1 - x) ^ 2 - 2), sq_nonneg ((1 - x) ^ 2 + x ^ 2), sq_nonneg (x * (1 - x) + 1), sq_nonneg (x * (1 - x) - 1)]
  · -- Second part: prove the existence of x and y such that (x^3 + 1) * (y^3 + 1) = 4
    use (1 + Real.sqrt 5) / 2, (1 - Real.sqrt 5) / 2
    constructor
    · -- Show x + y = 1
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ 5 by norm_num)]
    · -- Show (x^3 + 1) * (y^3 + 1) = 4
      have h1 : ((1 + Real.sqrt 5) / 2 : ℝ) * ((1 - Real.sqrt 5) / 2 : ℝ) = -1 := by
        nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ 5 by norm_num)]
      nlinarith [sq_nonneg ((1 + Real.sqrt 5) / 2 : ℝ), sq_nonneg ((1 - Real.sqrt 5) / 2 : ℝ),
        sq_nonneg ((1 + Real.sqrt 5) / 2 + (1 - Real.sqrt 5) / 2), sq_nonneg (( (1 + Real.sqrt 5) / 2 ) * ( (1 - Real.sqrt 5) / 2 ) + 1), sq_nonneg ( (Real.sqrt 5 : ℝ) ^ 2 - 5 ), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num ), h1 ]