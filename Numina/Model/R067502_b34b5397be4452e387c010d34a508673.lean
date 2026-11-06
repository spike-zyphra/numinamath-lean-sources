import Mathlib

theorem number_theory_4751 :
  IsLeast {n | ∃ k, n = k + (k+1) + (k+2) ∧ 5 ∣ k ∧ 8 ∣ (k+1) ∧ 9 ∣ (k+2)} 888 := by 
  constructor
  · -- Show that 888 is in the set
    use 295
    all_goals norm_num
  · -- Show that 888 is the least in the set
    intro n hn
    rcases hn with ⟨k, rfl, hk1, hk2, hk3⟩
    omega