import Mathlib

open Set Real

theorem algebra_130293 (a : ℝ) (A B : Set ℝ)
    (hA : A = Ico (-2) 4) (hB : B = {x | x ^ 2 - a * x - 4 ≤ 0})
    (hBA : B ⊆ A) :
    0 ≤ a ∧ a < 3 := by
  have h2 : (a + Real.sqrt (a ^ 2 + 16)) / 2 ∈ B := by
    rw [hB]
    have h3 : ((a + Real.sqrt (a ^ 2 + 16)) / 2) ^ 2 - a * ((a + Real.sqrt (a ^ 2 + 16)) / 2) - 4 ≤ 0 := by
      nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show 0 ≤ (a ^ 2 + (16 : ℝ)) by nlinarith)]
    exact h3

  have h4 : (a + Real.sqrt (a ^ 2 + 16)) / 2 ∈ A := hBA h2
  rw [hA] at h4
  have h6 : (a + Real.sqrt (a ^ 2 + 16)) / 2 < (4 : ℝ) := by
    have h7 : (a + Real.sqrt (a ^ 2 + 16)) / 2 < 4 := by
      linarith [h4.2]
    linarith

  have h2' : (a - Real.sqrt (a ^ 2 + 16)) / 2 ∈ B := by
    rw [hB]
    have h3 : ((a - Real.sqrt (a ^ 2 + 16)) / 2) ^ 2 - a * ((a - Real.sqrt (a ^ 2 + 16)) / 2) - 4 ≤ 0 := by
      nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show 0 ≤ (a ^ 2 + (16 : ℝ)) by nlinarith)]
    exact h3

  have h4' : (a - Real.sqrt (a ^ 2 + 16)) / 2 ∈ A := hBA h2'
  rw [hA] at h4'
  have h5' : (a - Real.sqrt (a ^ 2 + 16)) / 2 ≥ -2 := by
    have h6' : (a - Real.sqrt (a ^ 2 + 16)) / 2 ≥ -2 := by
      linarith [h4'.1]
    linarith

  have h7 : a ≥ 0 := by
    nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show 0 ≤ (a ^ 2 + (16 : ℝ)) by nlinarith), sq_nonneg (Real.sqrt (a ^ 2 + 16) - (a + 4))]

  have h8 : a < 3 := by
    nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show 0 ≤ (a ^ 2 + (16 : ℝ)) by nlinarith), sq_nonneg (Real.sqrt (a ^ 2 + 16) - (8 - a))]
  exact ⟨h7, h8⟩