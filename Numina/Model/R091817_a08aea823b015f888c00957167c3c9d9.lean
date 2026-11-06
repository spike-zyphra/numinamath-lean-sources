import Mathlib

def sol := ((Finset.Ico 1 200).filter (fun n => Odd (Nat.divisors n).card)).card

theorem number_theory_3279 : sol = 14 := by 
  native_decide