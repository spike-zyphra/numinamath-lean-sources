import Mathlib

theorem number_theory_847 : ∃ n : ℕ, (n % 7 = 0 ∧ n ≥ 1900 ∧ n ≤ 2099) ∨ (n % 7 = 6 ∧ n ≥ 1900 ∧ n ≤ 2099) := by
  exact ⟨1903, Or.inr ⟨by norm_num, by norm_num, by norm_num⟩⟩