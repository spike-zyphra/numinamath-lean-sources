import Mathlib

open Finset

theorem number_theory_237227 :
    {n : ℕ | n ∈ Icc 1 1000000 ∧ Odd (Nat.digits 10 n).sum}.ncard -
    {n : ℕ | n ∈ Icc 1 1000000 ∧ Even (Nat.digits 10 n).sum}.ncard ≠ 0 := by 
  have h1 : {n : ℕ | n ∈ Icc 1 1000000 ∧ Odd (Nat.digits 10 n).sum} = Finset.filter (fun n => Odd (Nat.digits 10 n).sum) (Icc 1 1000000) := by
    ext n
    simp
    <;> tauto
  have h2 : {n : ℕ | n ∈ Icc 1 1000000 ∧ Even (Nat.digits 10 n).sum} = Finset.filter (fun n => Even (Nat.digits 10 n).sum) (Icc 1 1000000) := by
    ext n
    simp
    <;> tauto
  rw [h1, h2]
  rw [Set.ncard_coe_Finset]
  rw [Set.ncard_coe_Finset]
  native_decide