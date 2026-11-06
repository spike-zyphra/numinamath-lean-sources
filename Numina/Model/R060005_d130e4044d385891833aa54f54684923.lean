import Mathlib

theorem number_theory_108308 (m n : ℕ) (hcoprime : Nat.Coprime m n) :
    Even n → ∃ d, d ∣ n ∧ d ∣ (2 * m + 3 * n) := by
  intro h
  exact ⟨1, by simp⟩