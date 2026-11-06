import Mathlib

open Finset Real Nat

theorem number_theory_611117: {n: ℕ | (10 ≤ n) ∧ (n ≤ 99) ∧ Even (Nat.divisors n).card }.encard = 84 := by
  have h1 : {n : ℕ | (10 ≤ n) ∧ (n ≤ 99) ∧ Even (Nat.divisors n).card } = 
    Finset.filter (fun n => Even (Nat.divisors n).card ) (Finset.Icc 10 99) := by
    ext n 
    simp
    <;> tauto
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide