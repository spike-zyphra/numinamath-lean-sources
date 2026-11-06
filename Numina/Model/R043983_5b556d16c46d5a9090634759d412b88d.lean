import Mathlib

theorem number_theory_110089 : Set.Infinite {p | p.Prime ∧ ∃ k, p = 8 * k + 1} := by
  have h1 : {p | p.Prime ∧ ∃ k, p = 8 * k + 1} = {p | p.Prime ∧ p % 8 = 1} := by
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    -- Assume p ∈ {p | p.Prime ∧ ∃ k, p = 8 * k + 1}
    · -- Assume h : p ∈ {p | p.Prime ∧ ∃ k, p = 8 * k + 1}
      rintro ⟨h_prime, ⟨k, hk⟩⟩
      refine ⟨h_prime, ?_⟩
      omega
    -- Assume p ∈ {p | p.Prime ∧ p % 8 = 1}
    · -- Assume h : p ∈ {p | p.Prime ∧ p % 8 = 1}
      rintro ⟨h_prime, h_mod⟩
      refine ⟨h_prime, ?_⟩
      refine ⟨(p - 1) / 8, ?_⟩
      omega
  rw [h1]
  apply Nat.infinite_setOf_prime_modEq_one
  all_goals norm_num