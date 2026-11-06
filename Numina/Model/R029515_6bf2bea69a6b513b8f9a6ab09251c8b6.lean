import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_193640 (f : ℝ → ℝ) (hf : f = λ x => -4 * x + 3 * sqrt (4 * x ^ 2 + 1)) :
    IsLeast (range f) (sqrt 5) := by
  constructor
  · -- Show sqrt 5 is in the range
    use Real.sqrt 5 / 5
    rw [hf]
    have h1 : -4 * (Real.sqrt 5 / 5 : ℝ) + 3 * Real.sqrt (4 * (Real.sqrt 5 / 5 : ℝ) ^ 2 + 1) = Real.sqrt 5 := by
      have h2 : (4 * (Real.sqrt 5 / 5 : ℝ) ^ 2 + 1 : ℝ) = (9 / 5 : ℝ) := by
        nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > (0 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      have h3 : Real.sqrt (4 * (Real.sqrt 5 / 5 : ℝ) ^ 2 + 1 : ℝ) = (3 * Real.sqrt 5 / 5 : ℝ) := by
        rw [h2]
        have h4 : Real.sqrt ((9 / 5 : ℝ)) = (3 * Real.sqrt 5 / 5 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> ring_nf
          <;> norm_num
          all_goals nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > (0 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        exact h4
      rw [h3]
      field_simp
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > (0 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    simpa using h1
  · -- Show sqrt 5 is the minimum
    intro y
    rintro ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    have h2 : -4 * x + 3 * Real.sqrt (4 * x ^ 2 + 1) ≥ Real.sqrt 5 := by
      have h1 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      by_cases h3 : -4 * x + 3 * Real.sqrt (4 * x ^ 2 + 1) ≥ 0
      · -- Case where the expression is ≥ 0
        nlinarith [Real.sqrt_nonneg (4 * x ^ 2 + 1), Real.sqrt_nonneg 5, Real.sqrt_nonneg (5), sq_nonneg (x - Real.sqrt 5 / 5), sq_nonneg (x + Real.sqrt 5 / 5), Real.sq_sqrt (show 0 ≤ (4 * x ^ 2 + 1 : ℝ) by nlinarith [sq_nonneg x]), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg (4 * x ^ 2 + 1)), sq_nonneg (Real.sqrt (4 * x ^ 2 + 1) - 3 * Real.sqrt 5 / 5), sq_nonneg (x - Real.sqrt 5 / 5), sq_nonneg (4 * x - 4 * (Real.sqrt 5 / 5)), mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (show (0 : ℝ) ≤ x ^ 2 by positivity)]
      · -- Case where the expression is < 0
        nlinarith [Real.sqrt_nonneg (4 * x ^ 2 + 1), Real.sqrt_nonneg 5, Real.sqrt_nonneg (5), sq_nonneg (x - Real.sqrt 5 / 5), sq_nonneg (x + Real.sqrt 5 / 5), Real.sq_sqrt (show 0 ≤ (4 * x ^ 2 + 1 : ℝ) by nlinarith [sq_nonneg x]), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg (4 * x ^ 2 + 1)), sq_nonneg (Real.sqrt (4 * x ^ 2 + 1) - 3 * Real.sqrt 5 / 5), sq_nonneg (x - Real.sqrt 5 / 5), sq_nonneg (4 * x - 4 * (Real.sqrt 5 / 5)), mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (show (0 : ℝ) ≤ x ^ 2 by positivity)]
    linarith