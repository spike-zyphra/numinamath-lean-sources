import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12542 :
  IsGreatest {t : ℝ | ∃ x y, x ≥ 0 ∧ y ≥ 0 ∧ x^2 + y^2 = 1 ∧ t = x * (x + y)} ((Real.sqrt 2 + 1) / 2) := by
  constructor
  · -- Show that $(Real.sqrt 2 + 1) / 2$ is in the set.
    use Real.sqrt (2 + Real.sqrt 2) / 2, Real.sqrt (2 + Real.sqrt 2) / 2 * (Real.sqrt 2 - 1)
    constructor
    · -- Show x ≥ 0
      have h1 : Real.sqrt (2 + Real.sqrt 2) ≥ 0 := Real.sqrt_nonneg (2 + Real.sqrt 2)
      have h2 : Real.sqrt (2 + Real.sqrt 2) / 2 ≥ 0 := by nlinarith
      nlinarith
    constructor
    · -- Show y ≥ 0
      have h1 : Real.sqrt (2 + Real.sqrt 2) ≥ 0 := Real.sqrt_nonneg (2 + Real.sqrt 2)
      have h2 : Real.sqrt 2 ≥ 1 := by
        have h2 : Real.sqrt 2 ≥ Real.sqrt 1 := Real.sqrt_le_sqrt (by norm_num)
        have h3 : Real.sqrt 1 = 1 := Real.sqrt_one
        have h4 : Real.sqrt 2 ≥ 1 := by linarith [h2, h3]
        linarith
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 + Real.sqrt 2 : ℝ) by positivity), Real.sqrt_nonneg (2 + Real.sqrt 2), Real.sqrt_nonneg 2]
    constructor
    · -- Show x^2 + y^2 = 1
      have h1 : Real.sqrt (2 + Real.sqrt 2) ^ 2 = 2 + Real.sqrt 2 := Real.sq_sqrt (by
        positivity
      )
      nlinarith [Real.sqrt_nonneg (2 + Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith), Real.sqrt_nonneg (2 : ℝ)]
    · -- Show t = x * (x + y)
      have h1 : Real.sqrt (2 + Real.sqrt 2) ^ 2 = 2 + Real.sqrt 2 := Real.sq_sqrt (by
        positivity
      )
      nlinarith [Real.sqrt_nonneg (2 + Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith), Real.sqrt_nonneg (2 : ℝ)]
  · -- Show that $(Real.sqrt 2 + 1) / 2$ is the greatest
    intro t ht
    rcases ht with ⟨x, y, hx1, hy1, h1, ht⟩
    nlinarith [sq_nonneg (x - Real.sqrt (2 + Real.sqrt 2) / 2), sq_nonneg (y - Real.sqrt (2 + Real.sqrt 2) / 2 * (Real.sqrt 2 - 1)), Real.sqrt_nonneg 2, Real.sqrt_nonneg (2 + Real.sqrt 2), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg (2 + Real.sqrt 2)), sq_nonneg (x - y), sq_nonneg (x * (Real.sqrt 2 - 1) - y), sq_nonneg (x * Real.sqrt 2 - y), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 + Real.sqrt 2 : ℝ) by positivity), Real.sqrt_nonneg (2 + Real.sqrt 2), Real.sqrt_nonneg 2, sq_nonneg (x - Real.sqrt (2 + Real.sqrt 2) / 2 * Real.sqrt 2 / (Real.sqrt 2 + 1)), sq_nonneg (y - Real.sqrt (2 + Real.sqrt 2) / 2 * (Real.sqrt 2 - 1) / (Real.sqrt 2 + 1)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 + Real.sqrt 2 : ℝ) by positivity), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg (2 + Real.sqrt 2)), Real.sqrt_nonneg (2 : ℝ)]