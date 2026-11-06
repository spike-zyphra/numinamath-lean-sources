import Mathlib

def is_increasing (n : ℕ) := n < (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) ∧
    (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) ∈ Finset.Icc 1000 9999

theorem number_theory_10573 :
    Set.ncard {n | is_increasing n} = 4005 := by 
  have h1 : {n | is_increasing n} = Finset.filter (fun n => n < (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) ∧
      (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) ∈ Finset.Icc 1000 9999) (Finset.Icc 0 9999) := by
    ext n
    simp [is_increasing, Finset.mem_Icc]
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide