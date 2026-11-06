import Mathlib

theorem number_theory_143329 : ∑ m ∈ (Finset.Icc 1 2018).filter (fun x => x % 10 = 8), m = 204626 := by 
  native_decide