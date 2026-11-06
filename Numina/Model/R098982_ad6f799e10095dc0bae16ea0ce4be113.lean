import Mathlib

theorem number_theory_45983 : {x | ∃ n, x = n ∧ n ≤ 2004 ∧ (Nat.divisors n).card % 2 = 1}.encard = 44 := by 
  have h1 : {x | ∃ n, x = n ∧ n ≤ 2004 ∧ (Nat.divisors n).card % 2 = 1} = Finset.filter (fun n => (Nat.divisors n).card % 2 = 1) (Finset.Iic 2004) := by 
    ext n
    simp 
    <;> try { 
      rw [Finset.mem_Iic]
      <;> tauto
    }
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide