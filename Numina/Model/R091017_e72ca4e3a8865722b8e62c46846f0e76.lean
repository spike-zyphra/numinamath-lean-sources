import Mathlib

def f (n m : ℕ) := n * (n - 1) / 2 + m

theorem number_theory_604892 :
    ∃ n m, f n m = 2015 := by
  exact ⟨63, 62, rfl⟩