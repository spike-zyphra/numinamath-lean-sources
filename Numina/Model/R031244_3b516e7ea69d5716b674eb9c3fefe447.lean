import Mathlib

theorem algebra_21012 : ∑ n in (Finset.Icc 100 200).filter (fun x => 7 ∣ x), n = 2107 := by
  native_decide