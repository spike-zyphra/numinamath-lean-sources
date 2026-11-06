import Mathlib

open Real Set

theorem algebra_310642 (x y : ℝ) (h₀ : x + 2 * y > 0) (h₁ : x - 2 * y > 0)
    (h₂ : (x + 2 * y) * (x - 2 * y) = 4) :
    abs x - abs y ≥ sqrt 3 ∧
    ∃ x y : ℝ, x + 2 * y > 0 ∧ x - 2 * y > 0 ∧ (x + 2 * y) * (x - 2 * y) = 4 ∧
    abs x - abs y = sqrt 3 := by
  have h3 : abs x - abs y ≥ Real.sqrt 3 := by
    have h4 : x ^ 2 - 4 * y ^ 2 = 4 := by
      nlinarith
    cases' abs_cases x with hx hx
    · cases' abs_cases y with hy hy
      · -- x ≥ 0, y ≥ 0
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), sq_nonneg (y - Real.sqrt 3 / 3), sq_nonneg (x - 4 * Real.sqrt 3 / 3)]
      · -- x ≥ 0, y < 0
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), sq_nonneg (y + Real.sqrt 3 / 3), sq_nonneg (x - 4 * Real.sqrt 3 / 3)]
    · cases' abs_cases y with hy hy
      · -- x < 0, y ≥ 0
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), sq_nonneg (y - Real.sqrt 3 / 3)]
      · -- x < 0, y < 0
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), sq_nonneg (y + Real.sqrt 3 / 3)]
  constructor
  · exact h3
  · use 4 * Real.sqrt 3 / 3, Real.sqrt 3 / 3
    constructor
    · -- Show x + 2 * y > 0
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_nonneg 3, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
    constructor
    · -- Show x - 2 * y > 0
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_nonneg 3, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
    constructor
    · -- Show (x + 2 * y) * (x - 2 * y) = 4
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith : (0 : ℝ) ≤ (3 : ℝ)), Real.sqrt_nonneg 3, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
    · -- Show abs x - abs y = sqrt 3
      have h4 : abs (4 * Real.sqrt 3 / 3) = 4 * Real.sqrt 3 / 3 := by
        apply abs_of_nonneg
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith : (0 : ℝ) < (3 : ℝ)), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith : (0 : ℝ) ≤ (3 : ℝ))]
      have h5 : abs (Real.sqrt 3 / 3) = Real.sqrt 3 / 3 := by
        apply abs_of_nonneg
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith : (0 : ℝ) < (3 : ℝ)), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith : (0 : ℝ) ≤ (3 : ℝ))]
      rw [h4, h5]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith : (0 : ℝ) < (3 : ℝ)), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith : (0 : ℝ) ≤ (3 : ℝ)), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]