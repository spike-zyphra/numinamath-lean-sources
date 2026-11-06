import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_159654 {a b : ℝ} (ha : a > b) (hab : a * b = 1) :
    IsLeast {x | ∃ a b : ℝ, a > b ∧ a * b = 1 ∧ x = (a^2 + b^2) / (a - b)} (2 * sqrt 2) := by
  constructor
  · -- Show that 2 * sqrt 2 is in the set
    use (Real.sqrt 2 + Real.sqrt 6) / 2, ( - Real.sqrt 2 + Real.sqrt 6) / 2
    constructor
    · -- Show a > b
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - Real.sqrt 6), Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (6 : ℝ) by norm_num)]
    constructor
    · -- Show a * b = 1
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6)]
    · -- Show x = (a^2 + b^2) / (a - b)
      field_simp [show Real.sqrt 2 > 0 by apply Real.sqrt_pos.mpr; norm_num, show Real.sqrt 6 > 0 by apply Real.sqrt_pos.mpr; norm_num]
      <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - Real.sqrt 6), Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (6 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6)]
  · -- Show that 2 * sqrt 2 is minimal
    intro x hx
    rcases hx with ⟨a, b, ha1, hab1, hx⟩
    have h1 : a - b > 0 := by linarith
    have h2 : a^2 + b^2 = (a - b)^2 + 2 := by
      have h3 : a * b = 1 := hab1
      nlinarith
    have h3 : (a^2 + b^2) / (a - b) = (a - b) + 2 / (a - b) := by
      have h4 : a - b > 0 := h1
      have h5 : a^2 + b^2 = (a - b)^2 + 2 := h2
      field_simp [h4]
      <;> nlinarith
    -- Prove that the expression is greater than 2 * sqrt 2
    have h4 : (a^2 + b^2) / (a - b) ≥ 2 * Real.sqrt 2 := by
      rw [h3]
      have h5 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
      have h6 : (a - b) + 2 / (a - b) - 2 * Real.sqrt 2 ≥ 0 := by
        have h8 : (a - b) > 0 := h1
        have h9 : (a - b) + 2 / (a - b) - 2 * Real.sqrt 2 = ((a - b)^2 + 2 - 2 * Real.sqrt 2 * (a - b) ) / (a - b) := by
          field_simp [h1]
          <;> ring
        rw [h9]
        have h10 : (a - b) ^ 2 + 2 - 2 * Real.sqrt 2 * (a - b) ≥ 0 := by
          nlinarith [sq_nonneg ((a - b) - Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
        apply div_nonneg
        linarith
        linarith
      linarith
    -- Show x is greater or equal
    linarith [h4, hx]