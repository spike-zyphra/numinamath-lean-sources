import Mathlib

theorem algebra_105493 (f : ℝ → ℝ) (hf : f = fun x => x^2 + 18 * x + 30) :
    ∃ x y, x ≠ y ∧ f x = 2 * Real.sqrt (x^2 + 18 * x + 45) ∧ f y = 2 * Real.sqrt (y^2 + 18 * y + 45) ∧ x * y = 20 := by
  use -9 + Real.sqrt 61, -9 - Real.sqrt 61
  constructor
  · -- Check that x ≠ y
    have h1 : Real.sqrt 61 > 0 := Real.sqrt_pos.mpr (show (61 : ℝ) > 0 by norm_num)
    have h2 : -9 + Real.sqrt 61 ≠ -9 - Real.sqrt 61 := by
      intro h
      have : Real.sqrt 61 = 0 := by linarith
      linarith [Real.sqrt_nonneg 61, this]
    exact h2
  constructor
  · -- Check f (-9 + Real.sqrt 61) = 2 * Real.sqrt ((-9 + Real.sqrt 61)^2 + 18 * (-9 + Real.sqrt 61) + 45)
    have hfx : f (-9 + Real.sqrt 61) = 10 := by
      rw [hf]
      simp
      nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show (0 : ℝ) ≤ (61 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (61 : ℝ) by norm_num)]
    have : 2 * Real.sqrt ((-9 + Real.sqrt 61) ^ 2 + 18 * (-9 + Real.sqrt 61) + 45) = 10 := by
      have h1 : ((-9 + Real.sqrt 61) ^ 2 + 18 * (-9 + Real.sqrt 61) + 45 : ℝ) = (25 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show (0 : ℝ) ≤ (61 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (61 : ℝ) by norm_num)]
      rw [h1]
      have h2 : Real.sqrt ((25 : ℝ) : ℝ) = 5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h2]
      norm_num
    rw [hfx]
    linarith
  constructor
  · -- Check f (-9 - Real.sqrt 61) = 2 * Real.sqrt ((-9 - Real.sqrt 61)^2 + 18 * (-9 - Real.sqrt 61) + 45)
    have hfy : f (-9 - Real.sqrt 61) = 10 := by
      rw [hf]
      simp
      nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show (0 : ℝ) ≤ (61 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (61 : ℝ) by norm_num)]
    have : 2 * Real.sqrt ((-9 - Real.sqrt 61) ^ 2 + 18 * (-9 - Real.sqrt 61) + 45) = 10 := by
      have h1 : ((-9 - Real.sqrt 61) ^ 2 + 18 * (-9 - Real.sqrt 61) + 45 : ℝ) = (25 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show (0 : ℝ) ≤ (61 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (61 : ℝ) by norm_num)]
      rw [h1]
      have h2 : Real.sqrt ((25 : ℝ) : ℝ) = 5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h2]
      norm_num
    rw [hfy]
    linarith
  · -- Check that the product of the two roots is 20
    nlinarith [Real.sqrt_nonneg 61, Real.sq_sqrt (show (0 : ℝ) ≤ (61 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (61 : ℝ) by norm_num)]