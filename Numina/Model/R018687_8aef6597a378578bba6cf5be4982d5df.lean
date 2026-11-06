import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_108457 {a : ℝ} (A B : Set ℝ)
  (hA : A = Ico (-2) 4) (hB : B = {x | x^2 - a * x - 4 ≤ 0}) :
  B ⊆ A ↔ 0 ≤ a ∧ a < 3 := by
  constructor 
  · -- Assume B ⊆ A, prove 0 ≤ a ∧ a < 3
    intro h
    have h2 : 0 ≤ a := by
      by_contra h2 
      push_neg at h2 
      have h3 : (a - Real.sqrt (a ^ 2 + 16) ) / 2 < -2 := by
        nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show (a ^ 2 + 16 : ℝ) ≥ 0 by nlinarith), sq_nonneg a ]
      have h4 : (a - Real.sqrt (a ^ 2 + 16) ) / 2 ∈ B := by
        rw [hB]
        have h5 : ( (a - Real.sqrt (a ^ 2 + 16) ) / 2 ) ^ 2 - a * ( (a - Real.sqrt (a ^ 2 + 16) ) / 2 ) - 4 ≤ (0 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show (a ^ 2 + 16 : ℝ) ≥ 0 by nlinarith), sq_nonneg ( (a - Real.sqrt (a ^ 2 + 16) ) / 2 - a / 2 ) ]
        simpa using h5
      have h6 : (a - Real.sqrt (a ^ 2 + 16) ) / 2 ∈ A := h h4
      rw [hA] at h6
      rcases h6 with ⟨h7, h8⟩
      nlinarith 
    have h3 : a < 3 := by
      by_contra h3 
      push_neg at h3 
      have h4 : (a + Real.sqrt (a ^ 2 + 16) ) / 2 ≥ (4 : ℝ) := by 
        nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show (a ^ 2 + 16 : ℝ) ≥ 0 by nlinarith), sq_nonneg (a - (4 : ℝ) ) ]
      have h5 : (a + Real.sqrt (a ^ 2 + 16) ) / 2 ∈ B := by
        rw [hB]
        have h6 : ( (a + Real.sqrt (a ^ 2 + 16) ) / 2 ) ^ 2 - a * ( (a + Real.sqrt (a ^ 2 + 16) ) / 2 ) - 4 ≤ (0 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show (a ^ 2 + 16 : ℝ) ≥ 0 by nlinarith), sq_nonneg ( (a + Real.sqrt (a ^ 2 + 16) ) / 2 - a / 2 ) ]
        simpa using h6 
      have h7 : (a + Real.sqrt (a ^ 2 + 16) ) / 2 ∈ A := h h5 
      rw [hA] at h7 
      rcases h7 with ⟨h8, h9⟩ 
      nlinarith 
    exact ⟨h2, h3⟩ 
  · -- Assume 0 ≤ a ∧ a < 3, prove B ⊆ A 
    rintro ⟨ha1, ha2⟩ 
    intro x hx 
    rw [hB] at hx 
    rw [hA]
    have h1 : x ^ 2 - a * x - 4 ≤ 0 := hx 
    have h2 : -2 ≤ x := by nlinarith [sq_nonneg (x - a / 2), Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show (a ^ 2 + 16 : ℝ) ≥ 0 by nlinarith) ]
    have h3 : x < 4 := by nlinarith [sq_nonneg (x - a / 2), Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show (a ^ 2 + 16 : ℝ) ≥ 0 by nlinarith) ]
    exact ⟨h2, h3⟩