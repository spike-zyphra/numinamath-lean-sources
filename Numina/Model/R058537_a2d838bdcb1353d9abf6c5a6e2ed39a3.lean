import Mathlib

theorem number_theory_3124 : ∑ m in (Finset.Ico 1 100).filter (fun m => (2017 * 2018 * 2019 * 2021)^m % 10 = 6), m = 2450 := by 
  native_decide