import Mathlib

theorem number_theory_213055 :
    Set.ncard {n : ℕ | n < 2019 ∧ (18 ∣ n ∨ 21 ∣ n) ∧ ¬(18 ∣ n ∧ 21 ∣ n)} = 176 := by
  have h1 : {n : ℕ | n < 2019 ∧ (18 ∣ n ∨ 21 ∣ n) ∧ ¬(18 ∣ n ∧ 21 ∣ n)} = Finset.filter (fun n => (18 ∣ n ∨ 21 ∣ n) ∧ ¬(18 ∣ n ∧ 21 ∣ n)) (Finset.Iio 2019) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide