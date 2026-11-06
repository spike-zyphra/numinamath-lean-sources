import Mathlib

theorem number_theory_258969 : {x | x > 0 ∧ x ∣ 23232}.encard = 42 := by
  have h1 : {x | x > 0 ∧ x ∣ 23232} = Finset.filter (fun x => x > 0) (Nat.divisors 23232) := by 
    ext n
    simp
    <;> try tauto
    <;> try aesop
    <;> try omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide