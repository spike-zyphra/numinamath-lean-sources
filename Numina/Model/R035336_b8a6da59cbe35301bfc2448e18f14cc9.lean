import Mathlib

theorem number_theory_256604 (n : ℕ) (h : n > 2) :
    ∃ m, IsSquare (m^2 + n^2) := by 
  use 0
  have h1 : IsSquare (0^2 + n^2) := by
    have h2 : 0 ^ 2 + n ^ 2 = n ^ 2 := by
      ring
    rw [h2]
    exact ⟨n, by ring⟩
  exact h1