import Mathlib
open Nat Finset

def is_balanced (n : ℕ) := if (Nat.digits 10 n).length = 4
    then (Nat.digits 10 n)[0]! + (Nat.digits 10 n)[1]! = (Nat.digits 10 n)[2]! + (Nat.digits 10 n)[3]! else False

theorem number_theory_98185 :
    Set.ncard {n | 1000 ≤ n ∧ n ≤ 9999 ∧ is_balanced n} = 615 := by
  have h1 : {n | 1000 ≤ n ∧ n ≤ 9999 ∧ is_balanced n} = Finset.filter (fun n => 
  (Nat.digits 10 n).length = 4 ∧ (Nat.digits 10 n)[0]! + (Nat.digits 10 n)[1]! = (Nat.digits 10 n)[2]! + (Nat.digits 10 n)[3]!
  ) (Finset.Icc 1000 9999) := by
    ext n
    simp [is_balanced]
    <;> try { omega }
    <;> try { native_decide }
  rw [h1] at *
  rw [Set.ncard_coe_Finset]
  native_decide