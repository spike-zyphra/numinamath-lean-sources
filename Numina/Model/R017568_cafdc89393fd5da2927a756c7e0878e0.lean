import Mathlib

theorem number_theory_121010 (f : ℕ → Fin 2) (h₀ : ∀ x y, f x = f y → f (3 * x + y) = f x)
    (h₁ : ∃ x, f x = 0) (h₂ : ∃ x, f x = 1) :
    ∀ n, f n = 0 ∨ f n = 1 := by
  intro n
  have h3 : f n = 0 ∨ f n = 1 := by
    have h4 : (f n).val < 2 := by 
      simp 
    have h5 : (f n).val = 0 ∨ (f n).val = 1 := by 
      omega 
    rcases h5 with (h5 | h5) 
    · 
      have h6 : f n = (0 : Fin 2) := by 
        simp [Fin.ext_iff, h5]
      left 
      exact h6 
    · 
      have h6 : f n = (1 : Fin 2) := by 
        simp [Fin.ext_iff, h5]
      right 
      exact h6 
  exact h3