import Mathlib

theorem number_theory_236154 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100 999 ∧ 15 ∣ n ∧ (Nat.digits 10 n).sum ≤ 9} = 23 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ 15 ∣ n ∧ (Nat.digits 10 n).sum ≤ 9} = Finset.filter (fun n => 15 ∣ n ∧ (Nat.digits 10 n).sum ≤ 9) (Finset.Icc 100 999) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide