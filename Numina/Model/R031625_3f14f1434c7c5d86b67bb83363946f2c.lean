import Mathlib

theorem number_theory_201190 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1 3400 ∧ 34 ∣ n ∧ (n.divisors.filter Odd).card = 2} = 7 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 3400 ∧ 34 ∣ n ∧ (n.divisors.filter Odd).card = 2} = Finset.filter (fun n => 34 ∣ n ∧ (n.divisors.filter Odd).card = 2) (Finset.Icc 1 3400) := by
    ext n
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide