import Mathlib

theorem number_theory_127380 :
    IsGreatest {x | ∃ n : ℕ, n ∈ Finset.Icc 100 999 ∧ x = n / (Nat.digits 10 n).sum} (100) := by 
  constructor
  · -- We verify that 100 is in the set, by taking n = 100
    use 100
    simp 
  · -- We need to prove that 100 is greatest in the set 
    intro x h 
    rcases h with ⟨n, hn, hx⟩ 
    rw [Finset.mem_Icc] at hn 
    rcases hn with ⟨hn1, hn2⟩ 
    interval_cases n <;> norm_num [hx] at *
    all_goals omega