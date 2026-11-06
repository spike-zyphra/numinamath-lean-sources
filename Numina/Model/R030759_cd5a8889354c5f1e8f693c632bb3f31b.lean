import Mathlib

theorem number_theory_114356 :
    Set.ncard {x : (ZMod 2014)ˣ | ∃ y : (ZMod 2014)ˣ, x * y = 1} = 936 := by

  have h3 : {x : (ZMod 2014)ˣ | ∃ y : (ZMod 2014)ˣ, x * y = 1} = (Set.univ : Set ((ZMod 2014)ˣ)) := by 
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_univ, true_and]
    have h4 : ∃ y : (ZMod 2014)ˣ, x * y = 1 := by 
      use x⁻¹ 
      simp [mul_inv_cancel]
    tauto

  rw [h3]
  have h4 : Set.ncard (Set.univ : Set ((ZMod 2014)ˣ)) = 936 := by 
    rw [Set.ncard_eq_toFinset_card']
    native_decide 
  exact h4