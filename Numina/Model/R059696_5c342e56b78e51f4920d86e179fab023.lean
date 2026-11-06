import Mathlib

theorem number_theory_6753 :
    Set.ncard {x : ℕ | x < 6006 ∧ Nat.Coprime x 6006} = 1440 := by 
  have h1 : {x : ℕ | x < 6006 ∧ Nat.Coprime x 6006} = Finset.filter (λ x => Nat.Coprime x 6006) (Finset.Iio 6006) := by 
    ext x 
    simp 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide