import Mathlib

theorem number_theory_199971 : ∃ n, n ∈ Finset.Icc 10000 99999 ∧ n % 1 = 0 ∧ n % 3 = 0 ∧ n % 5 = 0 ∧ n % 7 = 0 ∧ n % 9 = 0 ∧ n % 11 = 0 ∧ n % 13 = 0 ∧ n % 15 = 0 ∧ ¬(n % 2 = 0) ∧ ¬(n % 4 = 0) ∧ ¬(n % 6 = 0) ∧ ¬(n % 8 = 0) ∧ ¬(n % 10 = 0) ∧ ¬(n % 12 = 0) ∧ ¬(n % 14 = 0) ∧ ¬(n % 16 = 0) := by 
  use 45045
  constructor
  · -- Show 45045 is in the range [10000, 99999]
    exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num