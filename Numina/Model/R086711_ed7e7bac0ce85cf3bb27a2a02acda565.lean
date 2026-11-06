import Mathlib

theorem algebra_13823 :
    IsLeast {n | 0 < n ∧ n ≥ 100 ∧ 7 ∣ n} 105 := by 
  constructor 
  · -- Show 105 is in the set 
    exact ⟨by norm_num, by norm_num, by norm_num⟩ 
  · -- Show that 105 is the smallest such number in the set 
    intro n hn 
    rcases hn with ⟨hn_pos, hn_100, hn_div⟩ 
    omega