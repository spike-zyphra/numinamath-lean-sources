import Mathlib

set_option maxHeartbeats 600000

theorem algebra_19901 : 
  let I : Fin 4 → ℕ := fun i => Fin.casesOn i (fun val _ => match val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | _ => 0 );
  let II : Fin 5 → ℕ := fun i => Fin.casesOn i (fun val _ => match val with
  | 0 => 1
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 9
  | _ => 0 );
  let products := {x | ∃ i j, x = I i * II j };
  {x | ∃ i j, x = I i * II j ∧ Even x ∧ x ∈ Finset.Icc 10 99}.ncard / (4 * 5) = 7 / 20 := by
  intro I II products
  have h1 : {x | ∃ i j, x = I i * II j ∧ Even x ∧ x ∈ Finset.Icc 10 99} = 
          {10, 14, 18, 12, 20, 28, 36} := by 
    ext x 
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, 
      Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x in left side, need to show in right side
      rintro ⟨i, j, hx, heven, hx_range⟩
      fin_cases i <;> fin_cases j <;> simp [I, II, Nat.even_iff] at hx hx_range heven ⊢ 
      <;> omega 
    · -- Assume x in right side, need to show in left side 
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 10 
        refine' ⟨0, 2, by native_decide, by native_decide, by native_decide⟩ 
      · -- x = 14 
        refine' ⟨0, 3, by native_decide, by native_decide, by native_decide⟩ 
      · -- x = 18 
        refine' ⟨0, 4, by native_decide, by native_decide, by native_decide⟩ 
      · -- x = 12 
        refine' ⟨2, 1, by native_decide, by native_decide, by native_decide⟩ 
      · -- x = 20 
        refine' ⟨2, 2, by native_decide, by native_decide, by native_decide⟩ 
      · -- x = 28 
        refine' ⟨2, 3, by native_decide, by native_decide, by native_decide⟩ 
      · -- x = 36 
        refine' ⟨2, 4, by native_decide, by native_decide, by native_decide⟩ 
  rw [h1] 
  rw [Set.ncard_eq_toFinset_card']
  simp 
  <;> try native_decide