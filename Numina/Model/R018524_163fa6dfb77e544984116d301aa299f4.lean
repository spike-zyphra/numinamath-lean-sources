import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_311444 {A B : Set ℝ}
  (hA : A = {x | x + (5 - x) / (x - 2) = 2 * sqrt (x + 1)}) (hB : B = {x | x > 2}) :
  A ∩ B = {x | x = (5 + sqrt 13) / 2} := by
  ext x
  simp [hA, hB]
  constructor
  · -- Assume x ∈ A ∩ B, prove x = (5 + sqrt 13) / 2
    intro h
    rcases h with ⟨h_eq, hx⟩
    have h1 : x > 2 := hx
    have h2 : x - 2 ≠ 0 := by linarith
    have h3 : x + 1 ≥ 0 := by
      have h4 : x > 2 := h1
      linarith
    have h4 : x + (5 - x) / (x - 2) = 2 * sqrt (x + 1) := h_eq
    have h5 : x ^ 2 - 3 * x + 5 = 2 * (x - 2) * sqrt (x + 1) := by
      have h6 : x - 2 ≠ 0 := h2
      field_simp [h6] at h4 ⊢
      nlinarith [Real.sqrt_nonneg (x + 1)]
    have h6 : (x ^ 2 - 3 * x + 5) ^ 2 = 4 * (x - 2) ^ 2 * (x + 1) := by
      calc
        (x ^ 2 - 3 * x + 5) ^ 2 = (2 * (x - 2) * sqrt (x + 1)) ^ 2 := by rw [← h5]
        _ = 4 * (x - 2) ^ 2 * (sqrt (x + 1) ^ 2) := by ring
        _ = 4 * (x - 2) ^ 2 * (x + 1) := by 
          rw [Real.sq_sqrt]
          nlinarith
    have h7 : (x ^ 2 - 5 * x + 3) ^ 2 = 0 := by
      nlinarith
    have h8 : x ^ 2 - 5 * x + 3 = 0 := by
      apply pow_eq_zero 
      exact h7
    have h9 : x ^ 2 - 5 * x + 3 = 0 := h8
    have h10 : (x - (5 + Real.sqrt 13) / 2) * (x - (5 - Real.sqrt 13) / 2) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num : (13 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num : (13 : ℝ) ≥ 0)]
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- x - (5 + Real.sqrt 13) / 2 = 0
      linarith
    · -- x - (5 - Real.sqrt 13) / 2 = 0
      have h13 : x = (5 - Real.sqrt 13) / 2 := by linarith
      nlinarith [Real.sqrt_pos.mpr (show (13 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num : (13 : ℝ) ≥ 0)]
  · -- Assume x = (5 + sqrt 13) / 2, prove x ∈ A ∩ B
    intro h
    rw [h]
    constructor
    · -- Show the equation holds
      have h11 : Real.sqrt (13 : ℝ) ≥ 0 := Real.sqrt_nonneg 13
      have h14 : Real.sqrt ((5 + Real.sqrt 13) / 2 + 1) = (1 + Real.sqrt 13) / 2 := by
        have h110 : (5 + Real.sqrt 13) / 2 + 1 = (7 + Real.sqrt 13) / 2 := by nlinarith
        rw [h110]
        have h10 : Real.sqrt ((7 + Real.sqrt 13) / 2) = (1 + Real.sqrt 13) / 2 := by
          have h15 : ((1 + Real.sqrt 13) / 2) ^ 2 = (7 + Real.sqrt 13) / 2 := by
            nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
          have h16 : Real.sqrt ((7 + Real.sqrt 13) / 2) = (1 + Real.sqrt 13) / 2 := by
            have h10 : (1 + Real.sqrt 13) / 2 ≥ 0 := by
              nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
            have h30 : Real.sqrt (((1 + Real.sqrt 13) / 2) ^ 2) = (1 + Real.sqrt 13) / 2 := by
              rw [Real.sqrt_sq (h10)]
            rw [← h15]
            linarith
          exact h16
        exact h10
      have h13 : (5 + Real.sqrt 13) / 2 + (5 - (5 + Real.sqrt 13) / 2) / ((5 + Real.sqrt 13) / 2 - 2) = 2 * Real.sqrt ((5 + Real.sqrt 13) / 2 + 1) := by
        rw [h14]
        have h110 : (5 + Real.sqrt 13) / 2 - 2 = (1 + Real.sqrt 13) / 2 := by nlinarith
        have h111 : 5 - (5 + Real.sqrt 13) / 2 = (5 - Real.sqrt 13) / 2 := by nlinarith
        rw [h110, h111]
        have h112 : ((5 - Real.sqrt 13) / 2) / ((1 + Real.sqrt 13) / 2) = (Real.sqrt 13 - 3) / 2 := by
          field_simp [(show (1 + Real.sqrt 13 : ℝ) ≠ 0 by
            nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
          )]
          nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
        have h113 : (5 + Real.sqrt 13) / 2 + ((5 - Real.sqrt 13) / 2) / ((1 + Real.sqrt 13) / 2) = 1 + Real.sqrt 13 := by
          rw [h112]
          nlinarith
        nlinarith
      linarith
    · -- Show x > 2
      have h10 : Real.sqrt 13 > 0 := by
        apply Real.sqrt_pos.mpr
        norm_num
      nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]