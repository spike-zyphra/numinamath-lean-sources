import Mathlib

open Nat Real Finset Set
noncomputable section


theorem algebra_200004 :
  ∃ S : Finset ℕ, (S ⊆ Icc 1 100) ∧
    (∀ a ∈ S, ∀ b ∈ S, ∃ x : ℝ, x ^ 2 + (a : ℝ) * x + (b : ℝ) = 0) ∧
    S.card = 81 := by

  use Icc 20 100 
  constructor 
  · -- Show that Icc 20 100 ⊆ Icc 1 100 
    intro x hx 
    simp at hx ⊢ 
    omega 
  constructor 
  · -- Show that for all a, b ∈ S, there exists a real root 
    intro a ha b hb 
    have h1 : a ≥ 20 := by 
      simp at ha 
      omega 
    have h2 : a ≤ 100 := by 
      simp at ha 
      omega 
    have h3 : b ≥ 20 := by 
      simp at hb 
      omega 
    have h4 : b ≤ 100 := by 
      simp at hb 
      omega 
    have h1a : (a : ℝ) ≥ (20 : ℝ) := by 
      exact_mod_cast h1 
    have h2a : (a : ℝ) ≤ (100 : ℝ) := by 
      exact_mod_cast h2 
    have h3a : (b : ℝ) ≥ (20 : ℝ) := by 
      exact_mod_cast h3 
    have h4a : (b : ℝ) ≤ (100 : ℝ) := by 
      exact_mod_cast h4 
    have h7 : (a : ℝ) ^ 2 ≥ 4 * (b : ℝ) := by
      have h8 : (a : ℝ) ≥ (20 : ℝ) := by linarith 
      have h9 : (a : ℝ) ≤ (100 : ℝ) := by linarith 
      have h10 : (b : ℝ) ≥ (20 : ℝ) := by linarith 
      have h11 : (b : ℝ) ≤ (100 : ℝ) := by linarith 
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (a : ℝ) - (20 : ℝ) by nlinarith) (show (0 : ℝ) ≤ (100 : ℝ) - (b : ℝ) by nlinarith), sq_nonneg ((a : ℝ) - 20 : ℝ), sq_nonneg ((b : ℝ) - 100 : ℝ), sq_nonneg ((a : ℝ) - (b : ℝ)), sq_nonneg ((a : ℝ) - (2 * (b : ℝ)) ), sq_nonneg ((b : ℝ) - 20 : ℝ)]
    use (- (a : ℝ) / 2 + Real.sqrt ((a : ℝ) ^ 2 - 4 * (b : ℝ)) / 2)
    nlinarith [Real.sqrt_nonneg ((a : ℝ) ^ 2 - 4 * (b : ℝ)), Real.sq_sqrt (show 0 ≤ ((a : ℝ) ^ 2 - 4 * (b : ℝ)) by nlinarith [h7]
    )
]
  · -- Show S.card = 81 
    native_decide