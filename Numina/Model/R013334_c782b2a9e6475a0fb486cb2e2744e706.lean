import Mathlib

open Set Real

theorem algebra_303507 {a : ℝ} (B : Set ℝ) (hB : B = {x | x^2 - a * x - 4 ≤ 0}) :
    B ⊆ Ico (-2) 4 → a ∈ Ico 0 3 := by
  intro h
  have h1 : a ≥ 0 := by
    by_contra ha
    push_neg at ha
    have h2 : a < 0 := by linarith
    have h5 : (a - Real.sqrt (a ^ 2 + 16)) / 2 ∈ B := by
      rw [hB]
      have h6 : ((a - Real.sqrt (a ^ 2 + 16)) / 2) ^ 2 - a * ((a - Real.sqrt (a ^ 2 + 16)) / 2) - 4 ≤ 0 := by 
        nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show (a ^ 2 + 16) ≥ 0 by nlinarith)]
      exact h6
    have h7 : (a - Real.sqrt (a ^ 2 + 16)) / 2 ≥ -2 := by 
      have h8 : (a - Real.sqrt (a ^ 2 + 16)) / 2 ∈ B := h5
      have h9 : (a - Real.sqrt (a ^ 2 + 16)) / 2 ∈ Ico (-2) 4 := by 
        exact h h8
      simp at h9 ⊢
      all_goals linarith
    have h7' : (a - Real.sqrt (a ^ 2 + 16)) / 2 < -2 := by 
      nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show (a ^ 2 + 16) ≥ 0 by nlinarith)]
    linarith
  have h2 : a < 3 := by 
    by_contra ha
    push_neg at ha
    have h3 : a ≥ 3 := by linarith
    have h4 : (a + Real.sqrt (a ^ 2 + 16)) / 2 ∈ B := by 
      rw [hB]
      have h5 : ((a + Real.sqrt (a ^ 2 + 16)) / 2) ^ 2 - a * ((a + Real.sqrt (a ^ 2 + 16)) / 2) - 4 ≤ 0 := by
        nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show (a ^ 2 + 16) ≥ 0 by nlinarith)]
      exact h5
    have h8 : (a + Real.sqrt (a ^ 2 + 16)) / 2 < (4 : ℝ) := by 
      have h8' : (a + Real.sqrt (a ^ 2 + 16)) / 2 ∈ B := h4
      have h9 : (a + Real.sqrt (a ^ 2 + 16)) / 2 ∈ Ico (-2) 4 := by
        exact h h8'
      simp at h9 ⊢
      all_goals linarith
    have h9 : (a + Real.sqrt (a ^ 2 + 16)) / 2 ≥ (4 : ℝ) := by 
      nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show (a ^ 2 + 16) ≥ 0 by nlinarith)]
    linarith
  constructor
  · -- Show a ≥ 0
    linarith
  · -- Show a < 3
    linarith