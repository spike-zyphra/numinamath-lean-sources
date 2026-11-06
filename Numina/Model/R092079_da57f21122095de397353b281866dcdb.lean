import Mathlib

theorem number_theory_233372 :
    Set.ncard {x : ℕ | x ≤ 500 ∧ ¬2 ∣ x ∧ ¬3 ∣ x ∧ ¬5 ∣ x} = 134 := by 
  have h1 : {x : ℕ | x ≤ 500 ∧ ¬2 ∣ x ∧ ¬3 ∣ x ∧ ¬5 ∣ x} = Finset.filter (fun x => ¬2 ∣ x ∧ ¬3 ∣ x ∧ ¬5 ∣ x) (Finset.Iic 500) := by
    ext x
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide