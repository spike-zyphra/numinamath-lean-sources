import Mathlib

theorem number_theory_128611 :
    Set.ncard {x : ℕ | x < 2016 ∧ (x + 1) % 1 = 0 ∧ (x + 2) % 2 = 0 ∧ (x + 3) % 3 = 0 ∧ (x + 4) % 4 = 0 ∧ ¬(x + 5) % 5 = 0} = 134 := by 
  have h1 : {x : ℕ | x < 2016 ∧ (x + 1) % 1 = 0 ∧ (x + 2) % 2 = 0 ∧ (x + 3) % 3 = 0 ∧ (x + 4) % 4 = 0 ∧ ¬(x + 5) % 5 = 0} = Finset.filter (fun x => x < 2016 ∧ (x + 1) % 1 = 0 ∧ (x + 2) % 2 = 0 ∧ (x + 3) % 3 = 0 ∧ (x + 4) % 4 = 0 ∧ ¬(x + 5) % 5 = 0) (Finset.Icc 0 2015) := by
    ext x 
    simp 
    <;> omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide