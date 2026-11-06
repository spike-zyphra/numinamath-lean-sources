import Mathlib

theorem number_theory_246093 (m n : ℕ) (hmn : m.Coprime n) :
    ∃ s : Finset ℚ, 1 ∈ s ↔ m = n := by 
  use if m = n then ({1} : Finset ℚ) else (∅ : Finset ℚ)
  split_ifs with h
  · -- Assume m = n
    simp [h]
  · -- Assume m ≠ n
    simp [h]