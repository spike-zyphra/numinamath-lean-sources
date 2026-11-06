import Mathlib

theorem number_theory_110668 : ∃ n, 2013 ∣ n ∧ n % 10000 = 2014 := by 
  use 10222014
  constructor
  · norm_num
  · norm_num