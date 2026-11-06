import Mathlib

theorem algebra_21010 :
    IsGreatest {x | 30 ∣ x ∧ x < 520} 510 := by
  constructor
  · -- Show that 510 is in the set
    exact ⟨by norm_num, by norm_num⟩
  · -- Show that any element in the set is ≤ 510
    intro x h
    rcases h with ⟨hx1, hx2⟩
    have h1 : x ≤ 510 := by 
      omega
    linarith