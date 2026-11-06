import Mathlib

theorem number_theory_323418 :
    ∑ i ∈ Finset.Icc 1 30, i - ∑ i ∈ Finset.Icc 1 30, (if (Nat.digits 10 i).contains 2 then (Nat.ofDigits 10 (List.map (fun d => if d = 2 then 1 else d) (Nat.digits 10 i))) else i) = 103 := by 
  native_decide