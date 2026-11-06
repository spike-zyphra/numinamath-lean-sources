import Mathlib

open Mathlib


theorem number_theory_98649 :
Set.ncard {n | n < 1000 ∧ n % 2 ≠ n % 3 ∧ n % 2 ≠ n % 4 ∧ n % 2 ≠ n % 5 ∧ n % 2 ≠ n % 6 ∧ n % 3 ≠ n % 4 ∧ n % 3 ≠ n % 5 ∧ n % 3 ≠ n % 6 ∧ n % 4 ≠ n % 5 ∧ n % 4 ≠ n % 6 ∧ n % 5 ≠ n % 6} = 49 := by
  have h1 : {n | n < 1000 ∧ n % 2 ≠ n % 3 ∧ n % 2 ≠ n % 4 ∧ n % 2 ≠ n % 5 ∧ n % 2 ≠ n % 6 ∧ n % 3 ≠ n % 4 ∧ n % 3 ≠ n % 5 ∧ n % 3 ≠ n % 6 ∧ n % 4 ≠ n % 5 ∧ n % 4 ≠ n % 6 ∧ n % 5 ≠ n % 6} = Finset.filter (fun n => n < 1000 ∧ n % 2 ≠ n % 3 ∧ n % 2 ≠ n % 4 ∧ n % 2 ≠ n % 5 ∧ n % 2 ≠ n % 6 ∧ n % 3 ≠ n % 4 ∧ n % 3 ≠ n % 5 ∧ n % 3 ≠ n % 6 ∧ n % 4 ≠ n % 5 ∧ n % 4 ≠ n % 6 ∧ n % 5 ≠ n % 6) (Finset.Iic 999) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide