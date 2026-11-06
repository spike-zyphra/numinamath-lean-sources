import Mathlib

open Set Real

theorem algebra_10612 {a : ℝ} (A : Set ℝ) (hA : A = Ico (-2) 4) (B : Set ℝ)
    (hB : B = {x | x ^ 2 - a * x - 4 ≤ 0}) : B ⊆ A ↔ 0 ≤ a ∧ a < 3 := by
  constructor
  · -- Assume B ⊆ A, prove 0 ≤ a ∧ a < 3
    intro h
    have h1 : ∀ x : ℝ, x ∈ B → x ∈ A := by 
      simpa using h 
    have h3 : a ≥ 0 := by
      have h4 : ( (a - Real.sqrt (a^2 + 16)) / 2 ) ∈ B := by 
        rw [hB]
        have h5 : ( ( (a - Real.sqrt (a^2 + 16) ) / 2 ) ) ^ 2 - a * ( ( (a - Real.sqrt (a^2 + 16) ) / 2 ) ) - 4 ≤ 0 := by 
          nlinarith [Real.sqrt_nonneg (a^2 + 16), Real.sq_sqrt (show a^2 + 16 ≥ 0 by nlinarith)]
        simpa using h5 
      have h5 : ( (a - Real.sqrt (a^2 + 16)) / 2 ) ∈ A := h1 ( (a - Real.sqrt (a^2 + 16)) / 2 ) h4 
      rw [hA] at h5 
      rcases h5 with ⟨h51, h52⟩ 
      nlinarith [Real.sqrt_nonneg (a^2 + 16), Real.sq_sqrt (show a^2 + 16 ≥ 0 by nlinarith) ]
    have h4 : a < 3 := by
      have h5 : ( (a + Real.sqrt (a^2 + 16) ) / 2 ) ∈ B := by
        rw [hB]
        have h6 : ( ( (a + Real.sqrt (a^2 + 16) ) / 2 ) ) ^ 2 - a * ( ( (a + Real.sqrt (a^2 + 16) ) / 2 ) ) - 4 ≤ 0 := by 
          nlinarith [Real.sqrt_nonneg (a^2 + 16), Real.sq_sqrt (show a^2 + 16 ≥ 0 by nlinarith)]
        simpa using h6 
      have h6 : ( (a + Real.sqrt (a^2 + 16) ) / 2 ) ∈ A := h1 ( (a + Real.sqrt (a^2 + 16) ) / 2 ) h5 
      rw [hA] at h6
      rcases h6 with ⟨h61, h62⟩ 
      nlinarith [Real.sqrt_nonneg (a^2 + 16), Real.sq_sqrt (show a^2 + 16 ≥ 0 by nlinarith)]
    constructor 
    · linarith
    · linarith
  · -- Assume 0 ≤ a ∧ a < 3, prove B ⊆ A
    rintro ⟨ha1, ha2⟩ 
    intro x hx 
    have hx1 : x ^ 2 - a * x - 4 ≤ 0 := by 
      rw [hB] at hx 
      simpa using hx 
    have h4 : -2 ≤ x := by nlinarith [sq_nonneg (x - a / 2), sq_nonneg (x + 2), sq_nonneg (x - 4), sq_nonneg (a - 2 * x), sq_nonneg (a - 6), sq_nonneg (a), sq_nonneg (x - a), sq_nonneg (x - 2), sq_nonneg (a - 2)]
    have h5 : x < 4 := by nlinarith [sq_nonneg (x - a / 2), sq_nonneg (x - 4), sq_nonneg (x + 2), sq_nonneg (a - 2 * x), sq_nonneg (a - 6), sq_nonneg (a), sq_nonneg (x - a), sq_nonneg (x - 2), sq_nonneg (a - 2)]
    rw [hA]
    exact ⟨h4, h5⟩