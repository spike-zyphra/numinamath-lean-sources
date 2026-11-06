import Mathlib

open Polynomial
/-A polynomial P has four roots, 1/4, 1/2,2,4
The product of the roots is 1 , and P(1)=1. Find P(0).-/
theorem algebra_610853 {P: ℝ[X]} (h_roots: P.roots = {1/4, 1/2, 2, 4}) (h_val1: P.eval 1 = 1) 
(h_deg: P.natDegree = 4) : P.eval 0 = 8 / 9 := by
  -- Since `P` splits over ℝ, we can write it as `a * ∏ (X - r)` where `r ∈ roots P` --
  have hsplit : Splits (RingHom.id ℝ) P := by
    rw [Polynomial.splits_iff_card_roots]
    simp [h_roots, h_deg]
  have h1 := eval_eq_prod_roots_sub_of_splits_id hsplit 1
  rw [h_val1] at h1
   -- Now h1: 1 = leadingCoeff P * ∏ (1 - a) for a ∈ roots P --
  rw [h_roots] at h1
  simp at h1  -- Simplifies the product to explicit terms
  -- Compute the product (1 - 1/4) * (1 - 1/2) * (1 - 2) * (1 - 4) --

  -- Solve for leadingCoeff P --
  ring_nf at h1
  have h_leadingCoeff : leadingCoeff P = 8/9 := by
    nlinarith

  -- Now compute P(0) using the same theorem --
  have h0 := eval_eq_prod_roots_sub_of_splits_id hsplit 0
  rw [h_roots] at h0
  simp at h0  -- Simplifies to P(0) = leadingCoeff P * (0 - 1/4) * (0 - 1/2) * (0 - 2) * (0 - 4) --
  rw [h_leadingCoeff] at h0
  exact h0