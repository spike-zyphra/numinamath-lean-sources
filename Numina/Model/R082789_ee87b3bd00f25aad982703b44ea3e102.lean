import Mathlib

theorem number_theory_171341 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100000 999999 ∧ 5 ∣ n ∧ 9 ∣ (Nat.digits 10 n).sum} = 20000 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 100000 999999 ∧ 5 ∣ n ∧ 9 ∣ (Nat.digits 10 n).sum} = Finset.filter (λ n => 5 ∣ n ∧ 9 ∣ (Nat.digits 10 n).sum) (Finset.Icc 100000 999999) := by
    ext n
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide