import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_196993 (a b : ℝ) :
  (∀ x ∈ Icc 0 1, |x^2 + a * x + b| ≤ 1 / 8) ↔ a = -1 ∧ b = 1 / 8 := by
  constructor
  · -- Assume |x² + ax + b| ≤ 1/8 for all x ∈ [0,1], prove a = -1 and b = 1/8
    intro h
    have h1 := h 0 (by norm_num)
    have h2 := h 1 (by norm_num)
    have h3 := h (1 / 2) (by norm_num)
    have h4 := h (1 / 4) (by norm_num)
    have h5 := h (3 / 4) (by norm_num)
    have h11 : -1 / 8 ≤ b := by linarith [abs_le.mp h1]
    have h12 : b ≤ 1 / 8 := by linarith [abs_le.mp h1]
    have h21 : -1 / 8 ≤ 1 + a + b := by linarith [abs_le.mp h2]
    have h22 : 1 + a + b ≤ 1 / 8 := by linarith [abs_le.mp h2]
    have h31 : -1 / 8 ≤ (1 / 4 : ℝ) + (a / 2 : ℝ) + b := by 
      linarith [abs_le.mp h3]
    have h32 : (1 / 4 : ℝ) + (a / 2 : ℝ) + b ≤ 1 / 8 := by 
      linarith [abs_le.mp h3]
    have h41 : -1 / 8 ≤ (1 / 16 : ℝ) + (a / 4 : ℝ) + b := by 
      linarith [abs_le.mp h4]
    have h42 : (1 / 16 : ℝ) + (a / 4 : ℝ) + b ≤ 1 / 8 := by 
      linarith [abs_le.mp h4]
    have h51 : -1 / 8 ≤ (9 / 16 : ℝ) + (3 * a / 4 : ℝ) + b := by 
      linarith [abs_le.mp h5]
    have h52 : (9 / 16 : ℝ) + (3 * a / 4 : ℝ) + b ≤ 1 / 8 := by 
      linarith [abs_le.mp h5]

    constructor
    · -- Prove a = -1
      by_cases h7 : a < (-1 : ℝ)
      · -- Assume a < -1
        nlinarith [sq_nonneg (a + 1 : ℝ), sq_nonneg (b - 1 / 8 : ℝ), sq_nonneg (a * (a / 2)), sq_nonneg ((b) - (1 / 8 : ℝ)), sq_nonneg ((a / 4)), sq_nonneg ((b - 1 / 16 : ℝ))]
      · -- Assume a ≥ -1
        by_cases h8 : a > (-1 : ℝ)
        · -- Assume a > -1
          nlinarith [sq_nonneg (a + 1 : ℝ), sq_nonneg (b - 1 / 8 : ℝ), sq_nonneg (a * (a / 2)), sq_nonneg ((b) - (1 / 8 : ℝ)), sq_nonneg ((a / 4)), sq_nonneg ((b - 1 / 16 : ℝ))]
        · -- Assume a = -1
          nlinarith
    · -- Prove b = 1/8
      have h7 : a = -1 := by linarith
      nlinarith
  · -- Assume a = -1 and b = 1/8, prove |x² + ax + b| ≤ 1/8 for all x ∈ [0,1]
    rintro ⟨ha, hb⟩
    intro x hx
    rw [ha, hb]
    rw [mem_Icc] at hx
    have h1 : -1 / 8 ≤ x^2 - x + 1 / 8 := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    have h2 : x^2 - x + 1 / 8 ≤ 1 / 8 := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    have h3 : abs (x^2 - x + 1 / 8) ≤ 1 / 8 := by
      apply abs_le.mpr
      constructor <;> nlinarith
    simpa using h3