import Mathlib

open Nat

def crossSum (n : ℕ) := (Nat.digits 10 n).sum

def finalCrossSum (n : ℕ) := crossSum (crossSum n)

theorem number_theory_176776 :
    Set.ncard {n | 1 ≤ n ∧ n ≤ 1000 ∧ finalCrossSum n = 9} = 111 := by
  have h1 : {n | 1 ≤ n ∧ n ≤ 1000 ∧ finalCrossSum n = 9} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 1000 ∧ finalCrossSum n = 9) (Finset.Icc 0 1000) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide