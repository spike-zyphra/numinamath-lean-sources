import Mathlib

theorem number_theory_119649 (n : ℕ) :
    ∃ x : Fin n → ℕ, ∃ y : ℕ, ∑ i : Fin n, (x i)^2 = y^2 := by 
  use fun i => (0)
  use 0
  simp