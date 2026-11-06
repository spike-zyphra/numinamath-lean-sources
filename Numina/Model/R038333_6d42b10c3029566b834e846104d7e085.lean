import Mathlib

theorem algebra_13595 (S : Finset (Fin 52)) (hS : S.card = 52) :
    {x | x ∈ S ∧ (x / 4) = 4}.ncard / S.card = 1 / 13 := by

  have h1 : {x | x ∈ S ∧ (x / 4) = 4} = Finset.filter (fun x => (x / 4) = 4) S := by
    ext x
    simp
  rw [h1] at *
  rw [Set.ncard_coe_Finset]

  have h4 : S = Finset.univ := by 
    apply Finset.eq_of_subset_of_card_le 
    · -- Show that S ⊆ Finset.univ
      intro x hx
      simp at *
    all_goals
      simp at *
      all_goals omega

  have h2 : (Finset.filter (fun x => (x / 4) = 4) S).card = 4 := by
    rw [h4]
    native_decide
  
  calc
    (Finset.filter (fun x => (x / 4) = 4) S).card / S.card = 4 / 52 := by 
      rw [h2, hS]
    _ = 1 / 13 := by 
      all_goals norm_num