import Mathlib

theorem number_theory_13524 : IsGreatest {a : ℤ | a^9 ≤ 7^19} 60 := by 
  constructor 
  · -- Let's prove that 60 is in the set
    norm_num
  · -- Let's prove that 60 is the greatest in the set
    intro a ha
    have h : a^9 ≤ 7^19 := by 
      simpa using ha
    by_contra h'
    push_neg at h'
    have h1 : a ≥ 61 := by omega
    have h2 : a^9 ≥ 61^9 := by 
      apply pow_le_pow_left 
      all_goals omega 
    have h3 : 7^19 < 61^9 := by norm_num
    linarith