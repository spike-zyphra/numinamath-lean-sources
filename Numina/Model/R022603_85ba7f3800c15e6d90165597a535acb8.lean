import Mathlib

open Real
open scoped BigOperators

theorem inequalities_236532
  (A B C D E F : EuclideanSpace ℝ (Fin 2))
  (h₀ : D ∈ segment ℝ B C)
  (h₁ : E ∈ segment ℝ C A)
  (h₂ : F ∈ segment ℝ A B)
  (h₃ : D ≠ E)
  (h₄ : D ≠ F)
  (h₅ : E ≠ F)
  (h₆ : dist D E + dist E F + dist F D = (dist A B + dist B C + dist C A) / 2) :
  dist D E + dist E F + dist F D ≥ (dist A B + dist B C + dist C A) / 2 ∧
  dist D E ^ 2 + dist E F ^ 2 + dist F D ^ 2 ≥ (dist A B + dist B C + dist C A) ^ 2 / 12 := by

  constructor
  · -- Prove the first inequality: dist D E + dist E F + dist F D ≥ (dist A B + dist B C + dist C A) / 2
    linarith [h₆]

  · -- Prove the second inequality: dist D E ^ 2 + dist E F ^ 2 + dist F D ^ 2 ≥ (dist A B + dist B C + dist C A) ^ 2 / 12
    have h7 : dist D E ^ 2 + dist E F ^ 2 + dist F D ^ 2 ≥ (dist A B + dist B C + dist C A) ^ 2 / 12 := by
      have h₈ : dist D E ^ 2 + dist E F ^ 2 + dist F D ^ 2 - ((dist A B + dist B C + dist C A) ^ 2 / 12) ≥ 0 := by
        have h9 : (dist D E + dist E F + dist F D) = (dist A B + dist B C + dist C A) / 2 := by
          linarith [h₆]

        have h10 : dist D E ^ 2 + dist E F ^ 2 + dist F D ^ 2 ≥ ((dist D E + dist E F + dist F D) ^ 2) / 3 := by 
          linarith [sq_nonneg (dist D E - dist E F), sq_nonneg (dist E F - dist F D), sq_nonneg (dist F D - dist D E)]

        have h11_sub : dist D E ^ 2 + dist E F ^ 2 + dist F D ^ 2 ≥ ((dist A B + dist B C + dist C A) / 2) ^ 2 / 3 := by
          rw [show (dist D E + dist E F + dist F D) = (dist A B + dist B C + dist C A) / 2 by linarith [h₆]] at h10 
          linarith

        linarith [h11_sub]
      linarith
    exact h7