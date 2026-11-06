import Mathlib

theorem algebra_21156 : IsGreatest {n | 73 ∣ n ∧ n < 1000} 949 := by 
  constructor
  · -- Show that 949 is indeed in the set (divisible by 73 and less than 1000)
    constructor
    · -- Show that 73 divides 949
      norm_num
    · -- Show that 949 < 1000
      norm_num
  · -- Show that 949 is the greatest element in the set
    intro n hn
    rcases hn with ⟨hdiv, hn1⟩
    omega