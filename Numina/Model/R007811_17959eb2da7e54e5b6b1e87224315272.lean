import Mathlib

theorem algebra_14680 :
    Set.ncard {n : ℕ | 0 < n ∧ n < 60 ∧ Even (Nat.divisors n).card} = 52 := by
  have h1 : {n : ℕ | 0 < n ∧ n < 60 ∧ Even (Nat.divisors n).card} = Finset.filter (fun n => 0 < n ∧ n < 60 ∧ Even (Nat.divisors n).card) (Finset.Icc 0 59) := by
    ext n
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide