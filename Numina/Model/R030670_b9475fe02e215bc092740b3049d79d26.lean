import Mathlib

theorem number_theory_97677 : {x | x > 0 ∧ x ∣ (30^4) ∧ ¬(x = 1) ∧ ¬(x = 30^4)}.encard = 123 := by 
  have h1 : {x | x > 0 ∧ x ∣ (30^4) ∧ ¬(x = 1) ∧ ¬(x = 30^4)} = 
      Finset.filter (fun x => x > 0 ∧ x ∣ (30^4) ∧ ¬(x = 1) ∧ ¬(x = 30^4)) (Finset.Icc 1 (30^4)) := by 
    ext x
    simp
    intro hx1 hx2 hx3 hx4
    have h2 : x ≤ 30^4 := by 
      exact Nat.le_of_dvd (by norm_num) hx2 
    tauto
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide