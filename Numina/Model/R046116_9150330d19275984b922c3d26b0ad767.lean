import Mathlib

open Finset

theorem number_theory_54696 :
    ∀ N : ℕ, ∃ F : Polynomial ℤ, F.degree > N ∧ ∀ n : ℕ, ¬(F.eval 0 = 1 ∧
      ∀ c > 0, F.eval c > 0 ∧ {c | 0 < c ∧ Prime (F.eval c)}.encard = n) := by 
  intro N
  use (Polynomial.X ^ (N + 1) + Polynomial.C (0 : ℤ))
  constructor
  · -- Show that the degree is > N
    have h4 : ((Polynomial.X ^ (N + 1) + Polynomial.C (0 : ℤ) : Polynomial ℤ)).degree = (N + 1 : WithBot ℕ) := by
      compute_degree!
    have h4' : ((Polynomial.X ^ (N + 1) + Polynomial.C (0 : ℤ) : Polynomial ℤ)).degree > (N : WithBot ℕ) := by 
      rw [h4]
      have h : (N + 1 : WithBot ℕ) > (N : WithBot ℕ) := by 
        have h2 : (N + 1 : ℕ) > (N : ℕ) := by linarith
        exact_mod_cast h2
      exact h 
    exact_mod_cast h4' 
  · -- Show that there's no n such that the polynomial is n-good
    intro n h
    rcases h with ⟨h1, h2⟩
    exfalso 
    have eq1 : (Polynomial.X ^ (N + 1) + Polynomial.C (0 : ℤ) : Polynomial ℤ).eval 0 = 0 := by
      simp
    have eq2 : (Polynomial.X ^ (N + 1) + Polynomial.C (0 : ℤ) : Polynomial ℤ).eval 0 = 1 := h1
    -- This is 0 = 0 and 1, working
    omega