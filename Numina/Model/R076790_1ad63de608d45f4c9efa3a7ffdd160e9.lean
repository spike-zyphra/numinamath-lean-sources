import Mathlib

theorem number_theory_275377 (n : ℕ) :
    3 ∣ n + (n + 1) + (n + 2) := by
  have h : n + (n + 1) + (n + 2) = 3 * (n + 1) := by
    ring
  rw [h]
  exact ⟨n + 1, by ring⟩