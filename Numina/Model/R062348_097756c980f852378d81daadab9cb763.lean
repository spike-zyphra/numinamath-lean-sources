import Mathlib

theorem number_theory_128374 :
    Set.ncard {n : ℕ | n < 100 ∧ (2 ∣ n ∨ 3 ∣ n ∨ 5 ∣ n)} = 74 := by 
  have h1 : {n : ℕ | n < 100 ∧ (2 ∣ n ∨ 3 ∣ n ∨ 5 ∣ n)} = Finset.filter (λ n => 2 ∣ n ∨ 3 ∣ n ∨ 5 ∣ n) (Finset.Iio 100) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide