import Mathlib

theorem algebra_20932 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ ∀ d ∈ Nat.digits 10 n, Nat.Prime d} = 256 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ ∀ d ∈ Nat.digits 10 n, Nat.Prime d} = Finset.filter (fun n => ∀ d ∈ Nat.digits 10 n, Nat.Prime d) (Finset.Icc 1000 9999) := by 
    ext n 
    simp 
  rw [h1] 
  rw [Set.ncard_coe_Finset] 
  native_decide