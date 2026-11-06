import Mathlib

def is_increasing (n : ℕ) := n < (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n)))

theorem number_theory_204523 :
    Set.ncard {n | n ∈ Finset.Icc 1000 9999 ∧ is_increasing n} = 4005 := by
  have : {n | n ∈ Finset.Icc 1000 9999 ∧ is_increasing n} = Finset.filter (fun n => n < Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) (Finset.Icc 1000 9999) := by
    ext n
    simp [is_increasing]
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide