import Mathlib

theorem number_theory_95785 :
    (∑ i in Finset.Icc 1 30, i) - (∑ i in Finset.Icc 1 30, if (Nat.digits 10 i).contains 2 then (Nat.ofDigits 10 (List.map (fun d => if d = 2 then 1 else d) (Nat.digits 10 i))) else i) = 103 := by
  native_decide