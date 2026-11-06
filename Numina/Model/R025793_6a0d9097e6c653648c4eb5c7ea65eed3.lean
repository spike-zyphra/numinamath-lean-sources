import Mathlib

theorem number_theory_237234 (S : Finset ℕ) (hS : S = Finset.Icc 1 123) :
    Set.ncard {x | x ∈ S ∧ 4 ∣ ∑ i ∈ S \ {x}, i} = 31 := by 
  rw [hS] at *
  have : {x | x ∈ (Finset.Icc 1 123) ∧ 4 ∣ ∑ i ∈ (Finset.Icc 1 123) \ {x}, i} = Finset.filter (fun x => 4 ∣ ∑ i ∈ (Finset.Icc 1 123) \ {x}, i) (Finset.Icc 1 123) := by 
    ext x 
    simp 
  rw [this] 
  rw [Set.ncard_coe_Finset] 
  native_decide