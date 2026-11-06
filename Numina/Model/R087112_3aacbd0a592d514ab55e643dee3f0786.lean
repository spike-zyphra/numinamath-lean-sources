import Mathlib

theorem number_theory_211655 (a : Fin 6 → ℕ) (ha : ∑ i, a i = 2003 ^ 2003) :
    ∃ b : Fin 6 → ℕ, (∀ i, b i ≤ a i) ∧ (∀ i, b i - b (i - 1) - b (i + 1) = 0) := by 
  use (fun _ => 0)
  constructor
  · intro i
    simp 
  · intro i
    simp