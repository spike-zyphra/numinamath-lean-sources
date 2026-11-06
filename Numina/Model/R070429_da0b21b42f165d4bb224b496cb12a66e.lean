import Mathlib

open Real
open scoped BigOperators

theorem number_theory_134637 :
  (Set.ncard {x : ℕ | x ∈ Finset.Icc 1 2016 ∧ (Nat.digits 2 x).sum ≤ 8}) / 2016 = 655 / 672 := by 
  have h1 : {x : ℕ | x ∈ Finset.Icc 1 2016 ∧ (Nat.digits 2 x).sum ≤ 8} = Finset.filter (fun x => (Nat.digits 2 x).sum ≤ 8) (Finset.Icc 1 2016) := by
    ext x
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide