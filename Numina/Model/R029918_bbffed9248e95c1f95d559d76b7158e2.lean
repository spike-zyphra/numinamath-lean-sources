import Mathlib

open Finset

theorem number_theory_118385 (S : Set ℕ) (hS : ∀ n, n ∈ S → Nat.Prime n) :
    (∀ x : ℕ → ℕ, (∀ n, x n > 0) →
      ∃ M p, M > 0 ∧ p ∈ S ∧ ∀ n, p ^ M ∣ x n) ↔
    False := by 
  constructor
  · -- Assume the left side is true, prove False.
    intro h
    have h1 := h (fun _ => 1) (by
      intro n
      simp
    )
    rcases h1 with ⟨M, p, hm1, hp1, h2⟩
    have h3 := h2 0
    have h4 : p ^ M ∣ 1 := by
      simpa using h3
    have hp2 : p ≥ 2 := by
      have h5 : p ∈ S := hp1
      have h6 : Nat.Prime p := hS p h5
      have h7 : p ≥ 2 := by
        exact Nat.Prime.two_le h6
      linarith
    have hp4 : p ^ M ≥ 2 := by
      have hp5 : p ≥ 2 := hp2
      have hm2 : M ≥ 1 := by
        omega
      have : p ^ M ≥ 2 := by
        have h3 : p ^ 1 ≥ 2 := by
          simp [hp5]
        have h5 : p ^ M ≥ p ^ 1 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals
            omega
        have h7 : p ^ 1 = p := by
          ring
        nlinarith
      linarith
    have hp5 : p ^ M ≤ 1 := by
      exact Nat.le_of_dvd (show 0 < 1 by norm_num) h4
    linarith
  · -- Assume False, prove the statement.
    intro h
    cases h