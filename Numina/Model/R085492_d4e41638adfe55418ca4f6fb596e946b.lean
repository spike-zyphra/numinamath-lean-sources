import Mathlib

theorem number_theory_9969 : ∑ n in (Finset.Icc 1 1000).filter (fun x => (Nat.digits 10 x).contains 7), n = 157842 := by
  native_decide