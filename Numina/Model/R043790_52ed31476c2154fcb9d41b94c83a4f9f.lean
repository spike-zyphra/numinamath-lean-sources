import Mathlib

open Nat

theorem number_theory_7302 : {p : ℕ | p.Prime ∧ ∃ n, p = 4 * n + 1}.Infinite := by 
  have h1 : {p : ℕ | p.Prime ∧ ∃ n, p = 4 * n + 1} = {p : ℕ | p.Prime ∧ p % 4 = 1} := by 
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · -- Assume p ∈ {p : ℕ | p.Prime ∧ ∃ n, p = 4 * n + 1}
      rintro ⟨h_prime, ⟨n, hn⟩⟩
      have : p % 4 = 1 := by 
        have h1 : p = 4 * n + 1 := hn
        rw [h1]
        omega
      exact ⟨h_prime, this⟩
    · -- Assume p ∈ {p : ℕ | p.Prime ∧ p % 4 = 1}
      rintro ⟨h_prime, hp⟩
      have : ∃ n, p = 4 * n + 1 := by 
        refine' ⟨(p - 1) / 4, by omega⟩
      exact ⟨h_prime, this⟩
  rw [h1]
  apply Nat.infinite_setOf_prime_modEq_one
  all_goals norm_num