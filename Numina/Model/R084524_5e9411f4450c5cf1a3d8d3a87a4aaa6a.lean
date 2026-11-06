import Mathlib

theorem algebra_20786 :
    Set.ncard {n : ℕ | 0 < n ∧ 7 ∣ n ∧ n < 150} = 21 := by
  have h1 : {n : ℕ | 0 < n ∧ 7 ∣ n ∧ n < 150} = Finset.filter (fun n => 0 < n ∧ 7 ∣ n ∧ n < 150) (Finset.Iic 149) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide