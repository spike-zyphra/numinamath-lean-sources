import Mathlib.Tactic

theorem algebra_125696 (n : ℕ) :
    IsSquare (n * (n + 1) * (n + 2) * (n + 3) + 1) := by
  have h1 : n * (n + 1) * (n + 2) * (n + 3) + 1 = (n ^ 2 + 3 * n + 1) ^ 2 := by
    ring_nf
  rw [h1]
  exact ⟨n ^ 2 + 3 * n + 1, by ring⟩