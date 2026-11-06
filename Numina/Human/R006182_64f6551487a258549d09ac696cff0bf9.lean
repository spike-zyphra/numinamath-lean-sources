import Mathlib
open Finset Set Nat 
noncomputable section

theorem number_theory_60112233 :
  IsLeast { n : ℕ | n > 0 ∧ (Finset.Icc ⌈(n : ℚ) / 5⌉ ⌊(n : ℚ) / 2⌋).card = 25 } 80 := by
  -- Show that $n = 80$ is in the set.
  have h_n80_in_set : 80 ∈ { n : ℕ | n > 0 ∧ (Finset.Icc ⌈(n : ℚ) / 5⌉ ⌊(n : ℚ) / 2⌋).card = 25 } := by
    have h_n80_positive : (80 : ℕ) > 0 := by decide
    -- Compute the cardinality of Icc $⌈80/5⌉ ⌊80/2⌋$.
    have h_n80_card_25 : (Finset.Icc ⌈(80 : ℚ) / 5⌉ ⌊(80 : ℚ) / 2⌋).card = 25 := by
      have h_n80_ceil_div_5 : ⌈(80 : ℚ) / 5⌉ = 16 := by
        norm_num [Int.ceil_eq_iff]
      have h_n80_floor_div_2 : ⌊(80 : ℚ) / 2⌋ = 40 := by
        norm_num [Int.floor_eq_iff]
      rw [h_n80_ceil_div_5, h_n80_floor_div_2]
      rfl
    exact ⟨h_n80_positive, h_n80_card_25⟩  
  -- Show that $80$ is a lower bound for all n in the set.
  have h_n80_lower_bound : ∀ n' : ℕ, n' ∈ { n : ℕ | n > 0 ∧ (Finset.Icc ⌈(n : ℚ) / 5⌉ ⌊(n : ℚ) / 2⌋).card = 25 } → 80 ≤ n' := by
    intro n' h_n_prime
    have h_n_prime_positive : n' > 0 := h_n_prime.1
    have h_n_prime_card_25 : (Finset.Icc ⌈(n' : ℚ) / 5⌉ ⌊(n' : ℚ) / 2⌋).card = 25 := h_n_prime.2
    have h_n_prime_ge_80 : n' ≥ 80 := by
      by_contra h_contra
      have h_n_prime_le_79 : n' ≤ 79 := by linarith
      interval_cases n' <;> norm_num at h_n_prime_card_25 ⊢ <;>
      contradiction
    exact h_n_prime_ge_80
  exact ⟨h_n80_in_set, h_n80_lower_bound⟩
