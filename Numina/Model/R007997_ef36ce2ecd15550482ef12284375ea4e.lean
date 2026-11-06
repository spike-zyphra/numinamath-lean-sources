import Mathlib

theorem number_theory_15588 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ Odd (Nat.divisors n).card} = 6 := by 
  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ Odd (Nat.divisors n).card} = 
          Finset.filter (fun n => Odd (Nat.divisors n).card) (Finset.Icc 10 99) := by
    ext n
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide