import Mathlib

theorem number_theory_164595 (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 20) :
    ∃ x, x = ∑ a ∈ S, ∑ b ∈ S, if a < b then (a + b - 1) else (a + b + a * b) := by 
  refine' ⟨∑ a ∈ S, ∑ b ∈ S, if a < b then (a + b - 1) else (a + b + a * b), rfl⟩