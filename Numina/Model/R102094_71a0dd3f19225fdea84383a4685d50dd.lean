import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_295789 (a : ℝ) :
  (∀ x ∈ Icc 0 1, |x^2 - 2*a*x - a^2 - 3/4| ≤ 1) ↔
  a ∈ Icc (-1/2) (Real.sqrt 2 / 4) := by
  constructor
  · -- Assume that for all x in [0, 1], |x^2 - 2*a*x - a^2 - 3/4| ≤ 1
    intro h
    have h1 := h 0 (by norm_num)
    have h2 := h 1 (by norm_num)
    by_cases ha : a ≥ 0
    · by_cases ha1 : a ≤ 1
      · -- a ∈ [0, 1], need to apply h to a
        have h3 := h a (by
          constructor <;> linarith
        )
        constructor
        · -- Solving -1 ≤ a ≤ -1/2
          nlinarith [abs_le.mp h1, abs_le.mp h2]
        · -- Solving a ≤ sqrt(2)/4 from h3
          nlinarith [abs_le.mp h3, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      · -- a > 1
        constructor
        · -- Solving -1 ≤ a ≤ -1/2
          nlinarith [abs_le.mp h1, abs_le.mp h2]
        · -- Solving a ≤ sqrt(2)/4 from endpoints
          nlinarith [abs_le.mp h1, abs_le.mp h2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- a < 0
      constructor
      · -- Solving -1 ≤ a ≤ -1/2
        nlinarith [abs_le.mp h1, abs_le.mp h2]
      · -- Solving a ≤ sqrt(2)/4 from endpoints
        nlinarith [abs_le.mp h1, abs_le.mp h2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Assume a ∈ Icc (-1/2, Real.sqrt 2 / 4), prove that ∀ x ∈ Icc 0 1, |x^2 - 2*a*x - a^2 - 3/4| ≤ 1
    rintro ⟨h1, h2⟩
    intro x hx
    have h3 : 0 ≤ x := hx.1
    have h4 : x ≤ 1 := hx.2
    have h5 : x^2 - 2 * a * x - a^2 - 3 / 4 ≥ -1 := by
      nlinarith [sq_nonneg (x - a), sq_nonneg (x - 0), sq_nonneg (x - 1), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (a - Real.sqrt 2 / 4), sq_nonneg (a + 1 / 2)]
    have h6 : x^2 - 2 * a * x - a^2 - 3 / 4 ≤ 1 := by
      nlinarith [sq_nonneg (x - a), sq_nonneg (x - 0), sq_nonneg (x - 1), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (a - Real.sqrt 2 / 4), sq_nonneg (a + 1 / 2)]
    apply abs_le.mpr
    constructor <;> nlinarith