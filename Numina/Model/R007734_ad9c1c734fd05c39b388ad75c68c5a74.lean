import Mathlib

  theorem algebra_16084 :
    IsGreatest {x | 8 ∣ x ∧ 12 ∣ x ∧ x < 90} 72 := by 
  constructor
  · -- Show that 72 belongs to the set.
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  · -- Show that if x is in the set, then x ≤ 72.
    intro x hx
    rcases hx with ⟨hx8, hx12, hx90⟩
    omega