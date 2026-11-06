import Mathlib

theorem algebra_246057 (a b : ℤ) :
    ∃ f g : ℤ → ℤ, ∀ x, f (g x) = x + a ∧ g (f x) = x + b ↔ a = -b := by 
  use (fun x => -x), (fun x => -x - a)
  intro x 
  constructor 
  · -- Assume the equations hold, prove a = -b
    intro h
    rcases h with ⟨h1, h2⟩
    have eq : -(-x) - a = x + b := by 
      simpa using h2 
    linarith 
  · -- Assume a = -b, prove the equations
    intro h 
    have h1 : a = -b := by 
      linarith
    constructor
    · -- Show f (g x) = x + a 
      show -(-x - a) = x + a 
      ring 
    · -- Show g (f x) = x + b 
      show -(-x) - a = x + b 
      have h2 : -a = b := by 
        linarith [h1] 
      linarith