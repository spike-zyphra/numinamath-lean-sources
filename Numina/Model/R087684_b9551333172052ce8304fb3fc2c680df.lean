import Mathlib

theorem number_theory_597114 (n : ℕ) :
    ∃ m, √(n * (n + 1) * (n + 2) * (n + 3) + 1) = m := by 
  refine' ⟨√(n * (n + 1) * (n + 2) * (n + 3) + 1), rfl⟩