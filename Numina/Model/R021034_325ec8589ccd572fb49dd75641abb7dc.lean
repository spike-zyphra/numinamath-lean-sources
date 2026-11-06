import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_112082 {A B : Set ℝ} (fA : ℝ → ℝ)
  (hA : ∀ x, x ∈ A → fA x = 1) (hA' : ∀ x, x ∉ A → fA x = 0)
  (fB : ℝ → ℝ) (hB : ∀ x, x ∈ B → fB x = 1) (hB' : ∀ x, x ∉ B → fB x = 0) :
  (∀ x, fA x + fB x = 1) ↔ A = Bᶜ := by
  constructor
  · -- Assume that $f_A(x) + f_B(x) \equiv 1$ for all $x$, we need to prove $A = B^c$
    intro h
    ext x 
    constructor
    · -- Assume x ∈ A
      intro h1 
      have h1 : x ∈ A := h1 
      have h1' : fA x = 1 := by
        apply hA 
        exact h1 
      have h3 : fB x = 0 := by
        have h3 := h x 
        linarith 
      have h4 : x ∉ B := by 
        by_contra h5 
        have h5' : fB x = 1 := by 
          apply hB 
          exact h5 
        linarith 
      tauto 
    · -- Assume x ∉ B 
      intro h1 
      have h4 : x ∉ B := by 
        simpa using h1 
      have h5 : fB x = 0 := by 
        apply hB' 
        exact h4 
      have h2 := h x 
      have h6 : fA x = 1 := by 
        linarith 
      have h7 : x ∈ A := by 
        by_contra h8 
        push_neg at h8 
        have h8' : fA x = 0 := by 
          apply hA' 
          exact h8 
        linarith 
      assumption 
  · -- Assume $A = B^c$, we need to prove $f_A(x) + f_B(x) \equiv 1$
    intro h_eq 
    intro x 
    have h_eq' : x ∈ A ↔ x ∉ B := by 
      rw [h_eq] 
      simp 
    by_cases h1 : x ∈ A 
    · -- Assume x ∈ A 
      have h2 : fA x = 1 := by 
        apply hA 
        exact h1 
      have h1' : x ∉ B := by 
        tauto 
      have h5 : fB x = 0 := by 
        apply hB' 
        exact h1' 
      linarith 
    · -- Assume x ∉ A 
      have h6 : fA x = 0 := by 
        apply hA' 
        simpa using h1 
      have h1' : x ∈ B := by 
        by_contra h4 
        push_neg at h4 
        have h4' : x ∉ B := h4 
        have h5 : x ∈ A := by 
          tauto 
        contradiction 
      have h5 : fB x = 1 := by 
        apply hB 
        exact h1' 
      linarith