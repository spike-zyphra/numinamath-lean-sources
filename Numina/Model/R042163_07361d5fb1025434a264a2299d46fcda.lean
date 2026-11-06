import Mathlib

theorem number_theory_283995 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).length = 4 ∧
      (Nat.digits 10 n).toFinset = {1, 2, 3, 4} ∧ 11 ∣ n} = 8 := by
  have h3 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).length = 4 ∧
    (Nat.digits 10 n).toFinset = {1, 2, 3, 4} ∧ 11 ∣ n} = Finset.filter (fun n => (Nat.digits 10 n).length = 4 ∧ (Nat.digits 10 n).toFinset = {1, 2, 3, 4} ∧ 11 ∣ n) (Finset.Icc 1000 9999) := by 
    ext n
    simp 
    <;> tauto 
  rw [h3]
  rw [Set.ncard_coe_Finset]
  native_decide