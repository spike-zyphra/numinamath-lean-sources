import Mathlib

theorem number_theory_273770 :
    Set.ncard {n : ℕ | n < 5000 ∧ 11 ∣ n ∧ (Nat.digits 10 n).sum = 13} = 18 := by 
  have h1 : {n : ℕ | n < 5000 ∧ 11 ∣ n ∧ (Nat.digits 10 n).sum = 13} = Finset.filter (fun n => 11 ∣ n ∧ (Nat.digits 10 n).sum = 13) (Finset.Iio 5000) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide