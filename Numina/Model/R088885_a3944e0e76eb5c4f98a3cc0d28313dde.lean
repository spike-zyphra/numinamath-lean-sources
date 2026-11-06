import Mathlib

def f (n m : ℕ) := n * 8 + m

theorem number_theory_287135 : ∃ n m, f n m = 2020 := by 
  exact ⟨252, 4, by rfl⟩