import Mathlib

theorem number_theory_15771 :
    IsLeast {p | p.Prime ∧ ∃ n, p = n + 6 ∧ ¬(Nat.Prime (n + 1)) ∧ ¬(Nat.Prime (n + 2)) ∧ ¬(Nat.Prime (n + 3)) ∧ ¬(Nat.Prime (n + 4)) ∧ ¬(Nat.Prime (n + 5))} 29 := by 
  constructor 
  · -- Show 29 is in the set
    constructor
    · norm_num -- Check that 29 is prime
    · refine ⟨23, ?_⟩
      -- Verify all conditions with n = 23
      all_goals norm_num 
  · -- Show 29 is the least in the set 
    intro p hp
    rcases hp with ⟨h_prime, ⟨n, rfl, hn1, hn2, hn3, hn4, hn5⟩⟩
    by_contra h
    push_neg at h 
    have h1 : n < 23 := by linarith
    interval_cases n <;> norm_num at hn1 hn2 hn3 hn4 hn5 h_prime ⊢ <;> try contradiction
    <;> norm_num at *
    <;> try tauto