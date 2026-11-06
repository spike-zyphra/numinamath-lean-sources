import Mathlib

theorem algebra_19874 :
    Set.ncard {x | x ∈ [1, 2, 3, 4, 8, 14, 17, 29, 56, 91] ∧ (34 % x = 0 ∨ 7 ∣ x)} = 6 := by
  have h1 : {x | x ∈ [1, 2, 3, 4, 8, 14, 17, 29, 56, 91] ∧ (34 % x = 0 ∨ 7 ∣ x)} = {1, 2, 14, 17, 56, 91} := by
    ext x
    simp
    constructor
    · -- Assume x in the left, prove in the right
      intro h
      rcases h with ⟨hx1, hx2⟩
      rcases hx1 with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 1 
        simp at *
      · -- x = 2
        simp at *
      · -- x = 3
        exfalso 
        norm_num at hx2 
      · -- x = 4
        exfalso 
        norm_num at hx2 
      · -- x = 8
        exfalso 
        norm_num at hx2 
      · -- x = 14
        simp at *
      · -- x = 17
        simp at *
      · -- x = 29
        exfalso 
        norm_num at hx2 
      · -- x = 56
        simp at *
      · -- x = 91
        simp at *
    · -- Assume x in the right, prove in the left
      intro hx
      rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals 
      constructor <;> norm_num 
      <;> try trivial 
      all_goals try omega 
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  all_goals try native_decide