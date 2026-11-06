import Mathlib

theorem number_theory_204176 : ∑ n in (Finset.Icc 1 1000).filter (fun n => (Nat.digits 10 n).contains 7), n = 157842 := by
  native_decide