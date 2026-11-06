import Mathlib

theorem number_theory_19586 : (∏ i ∈ (Finset.Icc 2 98).filter (fun x => Even x ∧ ¬x % 10 = 0), i) % 10 = 6 := by
  native_decide