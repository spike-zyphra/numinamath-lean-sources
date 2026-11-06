import Mathlib

theorem number_theory_5370 : {x | x > 0 ∧ x ∣ 1848}.encard = 32 := by 
  have h1 : {x | x > 0 ∧ x ∣ 1848} = Finset.filter (fun x => x > 0) (1848).divisors := by 
    ext n 
    simp 
    <;> try { tauto } 
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide