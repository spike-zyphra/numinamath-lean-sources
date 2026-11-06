import Mathlib

theorem number_theory_261117 (n : ℕ) :
    ¬(n = 9 ∧ ∃ k, (23 - n) % 3 = 0 ∧ (23 - n) / 3 = k) := by
  intro h
  rcases h with ⟨hn_eq_9, ⟨k, hdiv1, hdiv2⟩⟩
  subst hn_eq_9
  omega