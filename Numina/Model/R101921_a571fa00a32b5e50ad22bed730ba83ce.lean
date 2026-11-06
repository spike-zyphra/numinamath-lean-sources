import Mathlib

theorem number_theory_107962 :
    11 ∣ ∑ n in (Finset.Icc 1000 9999).filter (fun n => (Nat.digits 10 n).length = 4 ∧
      (Nat.digits 10 n).toFinset.card = 4 ∧ (Nat.digits 10 n)[0]! * (Nat.digits 10 n)[3]! +
        (Nat.digits 10 n)[1]! * (Nat.digits 10 n)[2]! = 33), n := by 
  native_decide