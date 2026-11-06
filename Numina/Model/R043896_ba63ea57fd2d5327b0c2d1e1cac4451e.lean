import Mathlib

theorem number_theory_610021 :
    IsLeast {n : ℕ | n > 0 ∧ n % 3 = 2 ∧ n % 5 = 3 ∧ n % 7 = 4} 53 := by
  constructor
  · -- First, show that 53 belongs to the set 
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Now, show that if n is in the set, then n ≥ 53
    intro n hn
    rcases hn with ⟨hn_pos, hn_mod3, hn_mod5, hn_mod7⟩
    by_contra h
    push_neg at h 
    interval_cases n <;> norm_num at hn_mod3 hn_mod5 hn_mod7 hn_pos <;> omega