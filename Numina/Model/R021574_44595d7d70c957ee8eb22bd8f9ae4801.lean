import Mathlib

theorem algebra_169522 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x)
    (hper : ∀ x, f (x + 4) = f x) (hf : ∀ x ∈ Set.Ioo 0 2, f x = x ^ 2 - 16 * x + 60) :
    f (2 * Real.sqrt 10) = -36 := by

  have h1 : Real.sqrt 10 > 3 := by
    have h2 : Real.sqrt 9 < Real.sqrt 10 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h3 : Real.sqrt 9 = 3 := Real.sqrt_eq_cases.2 (by norm_num)
    linarith only [h2, h3, Real.sqrt_nonneg 10, Real.sqrt_nonneg 9]

  have h4 : 2 * Real.sqrt 10 > 4 := by
    nlinarith [h1]

  have h5 : f (2 * Real.sqrt 10) = f (2 * Real.sqrt 10 - 4) := by
    have h6 : f (2 * Real.sqrt 10 - 4 + 4) = f (2 * Real.sqrt 10 - 4) := hper (2 * Real.sqrt 10 - 4)
    rw [show 2 * Real.sqrt 10 - 4 + 4 = 2 * Real.sqrt 10 by ring] at h6
    linarith

  have h7 : 2 * Real.sqrt 10 - 4 > 2 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (10 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num), Real.sqrt_nonneg 10, h1]

  have h8 : 2 * Real.sqrt 10 - 4 < 4 := by
    have h9 : Real.sqrt 10 < 4 := by
      have h10 : Real.sqrt 9 < Real.sqrt 10 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h11 : Real.sqrt 9 = 3 := Real.sqrt_eq_cases.2 (by norm_num)
      have h12 : Real.sqrt 16 = 4 := Real.sqrt_eq_cases.2 (by norm_num)
      have h13 : Real.sqrt 10 < Real.sqrt 16 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith [h10, h11, h12, h13, Real.sqrt_nonneg 10, Real.sqrt_nonneg 16]
    nlinarith [h9]

  have h14 : f (2 * Real.sqrt 10 - 4) = - f (8 - 2 * Real.sqrt 10) := by
    have hx : (2 * Real.sqrt 10 - 4) - 4 = - (8 - 2 * Real.sqrt 10) := by ring
    have h15 : f (2 * Real.sqrt 10 - 4) = f ((2 * Real.sqrt 10 - 4) - 4) := by
      rw [← hper ((2 * Real.sqrt 10 - 4) - 4)]
      ring
    rw [h15]
    rw [hx]
    have h16 : f (-(8 - 2 * Real.sqrt 10)) = - f (8 - 2 * Real.sqrt 10) := hodd (8 - 2 * Real.sqrt 10)
    linarith [h16]

  have h17 : 8 - 2 * Real.sqrt 10 ∈ Set.Ioo 0 2 := by
    constructor
    · -- Show that 8 - 2*√10 > 0
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (10 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num), Real.sqrt_nonneg 10, h1]
    · -- Show that 8 - 2*√10 < 2
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (10 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num), Real.sqrt_nonneg 10, h1]

  have h18 : f (8 - 2 * Real.sqrt 10) = (8 - 2 * Real.sqrt 10) ^ 2 - 16 * (8 - 2 * Real.sqrt 10) + 60 := hf (8 - 2 * Real.sqrt 10) h17

  rw [h5, h14, h18]
  nlinarith [Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num)]