import Mathlib

theorem number_theory_16766 :
    IsGreatest {x | 0 < x ∧ x < 500 ∧ 3 ∣ x ∧ 4 ∣ x} 492 := by 
  constructor
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  · intro x h
    rcases h with ⟨hx1, hx2, hx3, hx4⟩
    have hx5 : x ≤ 492 := by 
      omega
    linarith