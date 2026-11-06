import Mathlib

theorem number_theory_3740 : {x | x > 0 ∧ x ∣ 4500}.encard = 36 := by
  have h1 : {x | x > 0 ∧ x ∣ 4500} = Finset.filter (fun x => x > 0) (Nat.divisors 4500) := by
    ext n
    simp
    <;> try { tauto }
    <;> try { native_decide }
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide