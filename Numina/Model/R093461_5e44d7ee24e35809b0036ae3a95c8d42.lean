import Mathlib

theorem number_theory_212696 (k : ℕ) (hk : k ≥ 6) :
    IsSquare (Nat.ofDigits k [1, 2, 3, 4, 5, 4, 3, 2, 1]) := by
  have h1 : Nat.ofDigits k [1, 2, 3, 4, 5, 4, 3, 2, 1] = (k^4 + k^3 + k^2 + k + 1) ^ 2 := by
    simp [Nat.ofDigits, List.foldl]
    ring
  rw [h1]
  exact ⟨k^4 + k^3 + k^2 + k + 1, by ring⟩