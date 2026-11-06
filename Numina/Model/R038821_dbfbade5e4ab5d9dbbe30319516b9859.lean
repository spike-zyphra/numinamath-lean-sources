import Mathlib

theorem number_theory_2820 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (n % 10) * 10 + (n / 10) = n + 9 ∧ Nat.Prime n} = 3 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (n % 10) * 10 + (n / 10) = n + 9 ∧ Nat.Prime n} = 
          Finset.filter (fun n => (n % 10) * 10 + (n / 10) = n + 9 ∧ Nat.Prime n) (Finset.Icc 10 99) := by
    ext n 
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide