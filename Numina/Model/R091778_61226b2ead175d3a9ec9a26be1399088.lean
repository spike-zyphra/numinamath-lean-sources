import Mathlib

theorem algebra_129604 {a : ℝ} (ha : a ≠ 0) :
    ∃ x y : ℤ, x^2 - (a + 1 / a) * x + (a + 4 * Real.sqrt 3) * (1 / a - 4 * Real.sqrt 3) = 0 ∧
    y^2 - (a + 1 / a) * y + (a + 4 * Real.sqrt 3) * (1 / a - 4 * Real.sqrt 3) = 0 ↔
    a = 7 - 4 * Real.sqrt 3 := by
  use 7, 7
  constructor
  · -- Assume 7 is a double root, prove a = 7 -4√3
    intro h
    rcases h with ⟨h₁, h₂⟩
    norm_num at h₁ h₂
    have h3 : a + 4 * Real.sqrt 3 = 7 := by
      field_simp at h₁
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), 
        Real.sqrt_nonneg 3, sq_nonneg (a - 7), sq_nonneg (a + 4 * Real.sqrt 3 - 7), sq_nonneg (Real.sqrt 3 - 4)]
    have h4 : a = 7 - 4 * Real.sqrt 3 := by
      linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith)]
    exact h4
  · -- Assume a = 7 -4√3, prove 7 is a double root
    intro h
    rw [h]
    constructor
    · -- First equation
      norm_num
      have h1 : Real.sqrt (3 : ℝ) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by linarith)
      field_simp [h1]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
    · -- Second equation
      norm_num
      have h1 : Real.sqrt (3 : ℝ) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by linarith)
      field_simp [h1]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]