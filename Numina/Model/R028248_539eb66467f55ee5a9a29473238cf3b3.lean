import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_317334 {f : ℝ → ℝ}
  (hf : f = λ x => ((x + 1)^2 + Real.sin x) / (x^2 + 1))
  (M N : ℝ)
  (hM : ∃ x, f x = M ∧ ∀ x, f x ≤ M)
  (hN : ∃ x, f x = N ∧ ∀ x, f x ≥ N) :
  M + N = 2 := by
  rcases hM with ⟨x1, hfx1, hM⟩
  rcases hN with ⟨x2, hfx2, hN⟩
  have h1 : ∀ x, f x + f (-x) = 2 := by
    intro x
    rw [hf]
    have eq111 : ((x + 1) ^ 2 + Real.sin x) / (x^ 2 + 1) + ((-x + 1) ^ 2 + Real.sin (-x)) / ((-x) ^ 2 + 1) = 2 := by
      have hx121 : ((-x) ^ 2 + 1) = (x ^ 2 + 1) := by
        ring
      have hx212 : Real.sin (-x) = - Real.sin x := by 
        rw [Real.sin_neg]
      rw [hx121, hx212]
      have eq111 : ((x + 1) ^ 2 + Real.sin x) / (x^ 2 + 1) + ((-x + 1) ^ 2 + -Real.sin x) / (x^ 2 + 1) = 2 := by 
        have hx1211 : ((x + 1) ^ 2 + Real.sin x) / (x^ 2 + 1) + ((-x + 1) ^ 2 + -Real.sin x) / (x^ 2 + 1) = 
            ((x + 1) ^ 2 + Real.sin x + ((-x + 1) ^ 2 + -Real.sin x) ) / (x^ 2 + 1) := by 
          have hx2222 : ((x + 1) ^ 2 + Real.sin x) / (x^ 2 + 1) + ((-x + 1) ^ 2 + -Real.sin x) / (x^ 2 + 1) = 
              ((x + 1) ^ 2 + Real.sin x + ((-x + 1) ^ 2 + -Real.sin x) ) / (x^ 2 + 1) := by 
            field_simp [show x^2 + 1 ≠ 0 by nlinarith [sq_nonneg x, Real.sin_sq_add_cos_sq x]]
            <;> ring_nf
          linarith [hx2222]
        rw [hx1211]
        have hx4444 : (x + 1) ^ 2 + Real.sin x + ((-x + 1) ^ 2 + -Real.sin x) = 2 * (x^2 + 1) := by 
          nlinarith [sq_nonneg x, Real.sin_sq_add_cos_sq x]
        have hx5555 : (x^2 + 1 : ℝ) ≠ 0 := by 
          nlinarith [sq_nonneg x, Real.sin_sq_add_cos_sq x]
        field_simp [show x^2 + 1 ≠ 0 by nlinarith [sq_nonneg x, Real.sin_sq_add_cos_sq x]]
        nlinarith [sq_nonneg x, Real.sin_sq_add_cos_sq x]
      exact_mod_cast eq111
    exact_mod_cast eq111
  have eq1 : f (-x1) = 2 - M := by
    have h2 : f x1 + f (-x1) = 2 := h1 x1
    have eq3 : f x1 = M := by linarith [hfx1]
    nlinarith
  have eq2 : f (-x2) = 2 - N := by 
    have h2 : f x2 + f (-x2) = 2 := h1 x2
    have eq3 : f x2 = N := by linarith [hfx2]
    nlinarith
  have h7 : N ≤ 2 - M := by
    have eq3 : f (-x1) ≥ N := by
      have h9 : ∀ x, f x ≥ N := hN
      specialize h9 (-x1)
      linarith [h9]
    nlinarith [eq1, eq3]
  have h8 : 2 - N ≤ M := by
    have eq4 : f (-x2) ≤ M := by
      have h10 : ∀ x, f x ≤ M := hM
      specialize h10 (-x2)
      linarith [h10]
    nlinarith [eq2, eq4]
  linarith [h7, h8]