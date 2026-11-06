import Mathlib

theorem number_theory_181703 :
    Set.ncard {n : ℕ | n < 2016 ∧ (2 ∣ n ∨ 3 ∣ n) ∧ ¬5 ∣ n} = 1075 := by 
  have h1 : {n : ℕ | n < 2016 ∧ (2 ∣ n ∨ 3 ∣ n) ∧ ¬5 ∣ n} = Finset.filter (fun x => (2 ∣ x ∨ 3 ∣ x) ∧ ¬5 ∣ x) (Finset.Iio 2016) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide