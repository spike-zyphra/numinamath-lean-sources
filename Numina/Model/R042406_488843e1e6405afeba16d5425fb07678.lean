import Mathlib

theorem algebra_14241 :
    IsGreatest {x | x < 100 ∧ Nat.gcd x 18 = 3} 93 := by 
  constructor 
  · -- Show that 93 is in the set 
    constructor 
    · norm_num 
    · norm_num [Nat.gcd]
  · -- Show that for any element in the set, it's ≤ 93
    intro x h
    rcases h with ⟨hx1, hx2⟩
    by_cases h4 : x ≤ 93
    · -- If x ≤ 93, we're done
      omega 
    · -- Assume x > 93
      have h5 : x > 93 := by 
        omega
      have h6 : x < 100 := by 
        omega 
      have h7 : x ≥ 94 := by 
        omega 
      interval_cases x <;> norm_num [Nat.gcd] at hx2 ⊢ <;> omega