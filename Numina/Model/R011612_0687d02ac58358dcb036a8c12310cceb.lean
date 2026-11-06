import Mathlib

theorem number_theory_265477 : 
  (Finset.range 10000).prod (fun i => (i + 1)) % 10^2499 = 0 ∧ 
  (Finset.range 10000).prod (fun i => (i + 1)) % 10^2500 ≠ 0 := by 
  native_decide