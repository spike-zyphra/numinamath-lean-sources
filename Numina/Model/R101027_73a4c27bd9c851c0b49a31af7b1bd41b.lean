import Mathlib

theorem number_theory_204323 :
    Set.ncard {n : ℕ | n < 500 ∧ n.divisors.card = 15} = 3 := by
  have h1 : {n : ℕ | n < 500 ∧ n.divisors.card = 15} = Finset.filter (fun n => n.divisors.card = 15) (Finset.Iio 500) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide