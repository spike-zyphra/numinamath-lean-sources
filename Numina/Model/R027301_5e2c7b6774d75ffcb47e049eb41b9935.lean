import Mathlib

theorem number_theory_99258 :
    Set.ncard {n : ℕ | Odd n ∧ n < 1000 ∧ (Nat.digits 10 n).prod = 252} = 5 := by
  have h1 : {n : ℕ | Odd n ∧ n < 1000 ∧ (Nat.digits 10 n).prod = 252} = 
          Finset.filter (fun n => Odd n ∧ n < 1000 ∧ (Nat.digits 10 n).prod = 252) (Finset.Icc (0 : ℕ) 999) := by 
    ext n
    simp [Nat.odd_iff]
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide