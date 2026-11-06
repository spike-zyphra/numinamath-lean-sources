import Mathlib

theorem number_theory_250239 :
    IsGreatest {n | n < 100} 99 ∧
    IsLeast {n | n > 300} 301 ∧
    IsGreatest {n | n ≤ 200} 200 ∧
    (99 + 301) / 200 = 2 := by
  constructor
  · -- Show 99 is greatest in {n < 100}
    constructor
    · -- Show 99 is in {n < 100}
      show 99 < 100
      all_goals norm_num
    · -- Show for all n in {n < 100}, n ≤ 99
      intro n hn
      have hn1 : n < 100 := by simp at hn ⊢; tauto
      omega
  constructor
  · -- Show 301 is least in {n > 300}
    constructor
    · -- Show 301 is in {n > 300}
      show 301 > 300
      all_goals norm_num
    · -- Show for all n in {n > 300}, 301 ≤ n
      intro n hn
      have hn1 : n > 300 := by simp at hn ⊢; tauto
      omega
  constructor
  · -- Show 200 is greatest in {n ≤ 200}
    constructor
    · -- Show 200 is in {n ≤ 200}
      show 200 ≤ 200
      all_goals norm_num
    · -- Show for all n in {n ≤ 200}, n ≤ 200
      intro n hn
      have hn1 : n ≤ 200 := by simp at hn ⊢; tauto
      omega
  · -- Show the final division is equal to 2
    all_goals norm_num