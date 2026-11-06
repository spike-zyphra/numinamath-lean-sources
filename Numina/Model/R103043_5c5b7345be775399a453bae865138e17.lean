import Mathlib

open Real

theorem number_theory_101576 :
    IsLeast {x : ℝ | ∃ n : ℕ, n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).length = 3 ∧
      (Nat.digits 10 n).toFinset.card = 3 ∧ x = n / ((Nat.digits 10 n).sum : ℝ)} (105 / 10) := by 
  constructor 
  · -- Show 105/10 is in the set
    use 189 
    constructor
    · norm_num [Finset.mem_Icc]
    constructor 
    · norm_num 
    constructor 
    · native_decide 
    · norm_num 
  · -- Show 105/10 is least 
    intro x hx 
    rcases hx with ⟨n, hn, h_dig_length, h_card, hx⟩ 
    rw [Finset.mem_Icc] at hn 
    rcases hn with ⟨hn₁, hn₂⟩
    by_contra h 
    push_neg at h 
    rw [hx] at h 
    interval_cases n <;> norm_num at h h_dig_length h_card hx <;> all_goals norm_num [hx] at h 
    <;> all_goals contradiction