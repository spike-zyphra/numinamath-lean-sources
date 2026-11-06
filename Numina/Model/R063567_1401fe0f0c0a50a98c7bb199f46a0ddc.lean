import Mathlib

def sumOfDigits (n : ℕ) := (Nat.digits 10 n).sum

theorem number_theory_3991 :
    Set.ncard {n | n ∈ Finset.Icc 10 99 ∧ sumOfDigits n ∣ n} = 23 := by
  have h : {n | n ∈ Finset.Icc 10 99 ∧ sumOfDigits n ∣ n} = Finset.filter (fun n => sumOfDigits n ∣ n) (Finset.Icc 10 99) := by
    ext n
    simp 
    <;> try { aesop }
  rw [h]
  rw [Set.ncard_coe_Finset]
  native_decide