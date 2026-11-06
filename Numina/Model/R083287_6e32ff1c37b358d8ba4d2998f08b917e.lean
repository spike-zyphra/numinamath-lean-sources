import Mathlib

theorem number_theory_249240 (n : ℕ) (hn : 2 ≤ n) :
    ∃ a : Fin n → ℕ,
      ∀ i j, i < j → ∃ k, (a j + a i) / (a j - a i) = k := by 
  use (fun _ => 0)
  intro i j h
  simp