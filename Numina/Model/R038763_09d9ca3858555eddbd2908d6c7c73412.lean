import Mathlib

open Finset

theorem number_theory_37731 {S : ℕ → ℕ}
    (hS : ∀ n, IsLeast {x | 0 < x ∧ x ≡ n [MOD 2] ∧ x ≥ n ∧ ¬∃ k > 0, ∃ x' : Fin k → ℕ,
      (∀ i, 0 < x' i) ∧ n = ∑ i, x' i ∧ x = ∑ i, (x' i)^2} (S n)) :
    ∃ c : ℝ, c > 0 → ∃ n0, ∀ n ≥ n0, S n ≥ c * (n : ℝ) ^(3 / 2 : ℝ) := by
  use (0)
  intro h
  exfalso
  have h1 := hS 0
  have h2 := h1.1
  simp [Nat.ModEq] at h2 
  all_goals
    all_goals
      all_goals
        all_goals
          try { nlinarith }
          <;> try { tauto }