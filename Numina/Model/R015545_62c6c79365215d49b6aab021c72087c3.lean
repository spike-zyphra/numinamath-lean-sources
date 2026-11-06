import Mathlib

open Set Real

theorem algebra_121012 {a : ℝ} (A B : Set ℝ)
    (hA : A = Ico (-2) 4) (hB : B = {x | x^2 - a * x - 4 ≤ 0}) :
    B ⊆ A ↔ 0 ≤ a ∧ a < 3 := by
  constructor
  · -- Assume B ⊆ A, prove 0 ≤ a ∧ a < 3
    intro h
    have h1 : (a - Real.sqrt (a ^ 2 + 16)) / 2 ≥ -2 := by
      have h2 : (a - Real.sqrt (a ^ 2 + 16)) / 2 ∈ B := by
        rw [hB]
        have hquad : ((a - Real.sqrt (a ^ 2 + 16)) / 2 : ℝ) ^ 2 - a * ((a - Real.sqrt (a ^ 2 + 16)) / 2) - 4 ≤ 0 := by
          nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 + 16 by nlinarith)]
        exact hquad
      have h3 : (a - Real.sqrt (a ^ 2 + 16)) / 2 ∈ A := h h2
      rw [hA] at h3
      simp at h3
      linarith
    have h2 : (a + Real.sqrt (a ^ 2 + 16)) / 2 < 4 := by
      have h4 : (a + Real.sqrt (a ^ 2 + 16)) / 2 ∈ B := by
        rw [hB]
        have hquad : ((a + Real.sqrt (a ^ 2 + 16)) / 2 : ℝ) ^ 2 - a * ((a + Real.sqrt (a ^ 2 + 16)) / 2) - 4 ≤ 0 := by
          nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 + 16 by nlinarith)]
        exact hquad
      have h5 : (a + Real.sqrt (a ^ 2 + 16)) / 2 ∈ A := h h4
      rw [hA] at h5
      simp at h5
      linarith
    have h3 : 0 ≤ a := by
      nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 + 16 by nlinarith)]
    have h4 : a < 3 := by
      nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 + 16 by nlinarith)]
    exact ⟨h3, h4⟩
  · -- Assume 0 ≤ a ∧ a < 3, prove B ⊆ A
    rintro ⟨ha1, ha2⟩
    intro x hx
    rw [hB] at hx
    have h1 : x ^ 2 - a * x - 4 ≤ 0 := hx
    rw [hA]
    constructor
    · -- Show x ≥ -2
      by_contra h
      push_neg at h
      have h5 : x < -2 := by linarith
      have h6 : x ^ 2 - a * x - 4 > 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) - a by linarith), sq_pos_of_pos (show (0 : ℝ) < (3 : ℝ) - a by linarith)]
      linarith
    · -- Show x < 4
      by_contra h
      push_neg at h
      have h7 : x ≥ 4 := by linarith
      have h8 : x ^ 2 - a * x - 4 > 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) - a by linarith), sq_pos_of_pos (show (0 : ℝ) < (3 : ℝ) - a by linarith)]
      linarith