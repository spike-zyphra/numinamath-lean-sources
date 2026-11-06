import Mathlib

theorem number_theory_17121 : ((Finset.Ioo 150 200 : Finset ℕ).filter (fun n => (n - 1) % 6 = 0)).sum id = 1575 := by
  native_decide