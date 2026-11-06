import Mathlib

theorem number_theory_165335 {n : ℕ} (hn : n > 0) (h : ∃ k, n = k^2 + 15 ∧ n + 18 = (k + 1)^2) :
    n = 271 := by
  rcases h with ⟨k, hn_eq, hn_add⟩
  rw [hn_eq] at hn_add
  have hk : k = 16 := by
    nlinarith
  rw [hk] at hn_eq
  nlinarith