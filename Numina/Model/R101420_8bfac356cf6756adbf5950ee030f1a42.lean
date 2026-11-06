import Mathlib

theorem algebra_117176 (mom dad kolya tanya : ℕ)
    (h₀ : dad = mom + 4) (h₁ : kolya = tanya + 4) (h₂ : kolya = dad / 2)
    (h₃ : mom + dad + kolya + tanya = 130) :
    mom = 42 ∧ dad = 46 ∧ kolya = 23 ∧ tanya = 19 := by 
  -- Solve linear system of equations usingomega.
  have h₄ : mom = 42 := by 
    omega
  -- Now derive the other variables from h₄ and the given equations.
  have h₅ : dad = 46 := by 
    omega
  have h₆ : kolya = 23 := by 
    omega
  have h₇ : tanya = 19 := by 
    omega
  exact ⟨h₄, h₅, h₆, h₇⟩