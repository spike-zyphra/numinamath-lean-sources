import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_327906 (a b : ℝ)
  (h : ∀ x ∈ Icc 0 1, |a * x + b - sqrt (1 - x ^ 2)| ≤ (sqrt 2 - 1) / 2) :
  a = -1 ∧ b = (sqrt 2 + 1) / 2 := by
  have h1 := h 0 (by norm_num)
  have h2 := h 1 (by norm_num)
  have h3 := h (Real.sqrt (1 / 2)) (by
    constructor
    · -- Show sqrt(1/2) ≥ 0
      nlinarith [Real.sqrt_nonneg (1 / 2), Real.sq_sqrt (show 0 ≤ (1 / 2 : ℝ) by norm_num)]
    · -- Show sqrt(1/2) ≤ 1
      nlinarith [Real.sqrt_nonneg (1 / 2), Real.sq_sqrt (show 0 ≤ (1 / 2 : ℝ) by norm_num), Real.sqrt_nonneg (1 / 2)]
  )
  have h11 : - (sqrt 2 - 1) / 2 ≤ b - 1 := by
    have h1' : |a * (0 : ℝ) + b - sqrt (1 - (0 : ℝ) ^ 2)| ≤ (sqrt 2 - 1) / 2 := by
      simpa using h1
    have h111 : |a * (0 : ℝ) + b - sqrt (1 - (0 : ℝ) ^ 2)| = |b - 1| := by
      have h11 : a * (0 : ℝ) + b - sqrt (1 - (0 : ℝ) ^ 2) = b - 1 := by
        have h10 : sqrt (1 - (0 : ℝ) ^ 2) = 1 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h10]
        <;> nlinarith
      rw [h11]
      <;> norm_num [abs_sub]
    rw [h111] at h1'
    linarith [abs_le.mp h1']
  have h12 : b - 1 ≤ (sqrt 2 - 1) / 2 := by
    have h1' : |a * (0 : ℝ) + b - sqrt (1 - (0 : ℝ) ^ 2)| ≤ (sqrt 2 - 1) / 2 := by
      simpa using h1
    have h111 : |a * (0 : ℝ) + b - sqrt (1 - (0 : ℝ) ^ 2)| = |b - 1| := by
      have h11 : a * (0 : ℝ) + b - sqrt (1 - (0 : ℝ) ^ 2) = b - 1 := by
        have h10 : sqrt (1 - (0 : ℝ) ^ 2) = 1 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h10]
        <;> nlinarith
      rw [h11]
      <;> norm_num [abs_sub]
    rw [h111] at h1'
    linarith [abs_le.mp h1']
  have h21 : - (sqrt 2 - 1) / 2 ≤ a + b := by
    have h2' : |a * (1 : ℝ) + b - sqrt (1 - (1 : ℝ) ^ 2)| ≤ (sqrt 2 - 1) / 2 := by
      simpa using h2
    have h122 : |a * (1 : ℝ) + b - sqrt (1 - (1 : ℝ) ^ 2)| = |a + b| := by
      have h11 : a * (1 : ℝ) + b - sqrt (1 - (1 : ℝ) ^ 2) = a + b := by
        have h10 : sqrt (1 - (1 : ℝ) ^ 2) = (0 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h10]
        <;> nlinarith
      rw [h11]
      <;> norm_num [abs_sub]
    rw [h122] at h2'
    linarith [abs_le.mp h2']
  have h22 : a + b ≤ (sqrt 2 - 1) / 2 := by
    have h2' : |a * (1 : ℝ) + b - sqrt (1 - (1 : ℝ) ^ 2)| ≤ (sqrt 2 - 1) / 2 := by
      simpa using h2
    have h122 : |a * (1 : ℝ) + b - sqrt (1 - (1 : ℝ) ^ 2)| = |a + b| := by
      have h11 : a * (1 : ℝ) + b - sqrt (1 - (1 : ℝ) ^ 2) = a + b := by
        have h10 : sqrt (1 - (1 : ℝ) ^ 2) = (0 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h10]
        <;> nlinarith
      rw [h11]
      <;> norm_num [abs_sub]
    rw [h122] at h2'
    linarith [abs_le.mp h2']
  have h31 : sqrt (1 - (Real.sqrt (1 / 2)) ^ 2) = Real.sqrt (1 / 2) := by
    have h4 : (Real.sqrt (1 / 2) ) ^ 2 = (1 / 2 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    have h421 : (1 - (Real.sqrt (1 / 2)) ^ 2 : ℝ) = (1/2 : ℝ) := by
      linarith [h4]
    rw [h421]
    all_goals norm_num [Real.sqrt_eq_iff_sq_eq]
    <;> linarith
    all_goals norm_num [Real.sqrt_eq_iff_sq_eq]
    <;> linarith
  have h35 : |a * Real.sqrt (1 / 2) + b - Real.sqrt (1 - (Real.sqrt (1 / 2)) ^ 2)| ≤ (sqrt 2 - 1) / 2 := by
    simpa [show Real.sqrt (1 - (Real.sqrt (1 / 2)) ^ 2) = Real.sqrt (1/2) by
        linarith [Real.sq_sqrt (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num), h31]
    ] using h3
  have h41 : - (sqrt 2 - 1) / 2 ≤ a * Real.sqrt (1 / 2) + b - Real.sqrt (1 - (Real.sqrt (1 / 2)) ^ 2) := by
    linarith [abs_le.mp h35]
  have h42 : a * Real.sqrt (1 / 2) + b - Real.sqrt (1 - (Real.sqrt (1 / 2)) ^ 2) ≤ (sqrt 2 - 1) / 2 := by
    linarith [abs_le.mp h35]
  have h6 : b = (sqrt 2 + 1) / 2 := by
    have h42' : Real.sqrt (1 - (Real.sqrt (1 / 2)) ^ 2) = Real.sqrt (1/2) := by
      have h411 : (Real.sqrt (1 / 2) ) ^ 2 = (1 / 2 : ℝ) := by
        rw [Real.sq_sqrt]
        norm_num
      have h421 : (1 - (Real.sqrt (1 / 2)) ^ 2 : ℝ) = (1/2 : ℝ) := by
        linarith [h411]
      rw [h421]
      all_goals norm_num [Real.sqrt_eq_iff_sq_eq]
      <;> linarith
      all_goals norm_num [Real.sqrt_eq_iff_sq_eq]
      <;> linarith
    rw [h42'] at h41 h42
    have h60 : (Real.sqrt (1 / 2) : ℝ) = sqrt 2 / 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h60] at h41 h42
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sqrt_nonneg (2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), sq_nonneg (sqrt 2 ^ 2 - 1 / 2), Real.sqrt_nonneg (2 / 2), sq_nonneg (sqrt 2 ^ 2 - 1), sq_nonneg (sqrt 2 ^ 2 - 2)]
  have ha : a = -1 := by
    have h60 : (Real.sqrt (1 / 2) : ℝ) = sqrt 2 / 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h42' : Real.sqrt (1 - (Real.sqrt (1 / 2)) ^ 2) = Real.sqrt (1/2) := by
      have h411 : (Real.sqrt (1 / 2) ) ^ 2 = (1 / 2 : ℝ) := by
        rw [Real.sq_sqrt]
        norm_num
      have h421 : (1 - (Real.sqrt (1 / 2)) ^ 2 : ℝ) = (1/2 : ℝ) := by
        linarith [h411]
      rw [h421]
      all_goals norm_num [Real.sqrt_eq_iff_sq_eq]
      <;> linarith
    rw [h42'] at h41 h42
    rw [h60] at h41 h42
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sqrt_nonneg (2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), sq_nonneg (sqrt 2 ^ 2 - 1 / 2), Real.sqrt_nonneg (2 / 2), sq_nonneg (sqrt 2 ^ 2 - 1), sq_nonneg (sqrt 2 ^ 2 - 2), h6]
  constructor
  · -- Show a = -1
    exact ha
  · -- Show b = (sqrt 2 + 1) / 2
    exact h6