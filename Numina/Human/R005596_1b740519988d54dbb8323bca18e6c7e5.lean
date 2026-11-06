import Mathlib

open Real

/-
Problem:
Calculate the probability that when rolling four 6-sided dice, at least three show the same value.
-/
theorem Combinatorics_609043 
  (P₁ : ℝ)
  (AP₁ : P₁ = P₂ / P₃)
  (AP₂ : P₂ = P₄ + P₅)
  (AP₃ : P₃ = 6 * 6 * 6 * 6)
  (AP₄ : P₄ = Nat.choose 6 1)
  (AP₅ : P₅ = Nat.choose 6 1 * Nat.choose 4 3 * (6 - 1)) :
  P₁ = (7 / 72 : ℝ) := by 

  simp_all

  ring_nf


  

