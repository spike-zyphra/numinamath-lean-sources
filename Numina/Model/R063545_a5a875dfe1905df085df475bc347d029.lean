import Mathlib

theorem number_theory_264989 : {x : ℕ × ℕ | x.1 * 17 + x.2 * 5 = 453}.ncard = 5 := by

  have h1 : {x : ℕ × ℕ | x.1 * 17 + x.2 * 5 = 453} = {(4, 77), (9, 60), (14, 43), (19, 26), (24, 9)} := by 
    ext ⟨a, b⟩
    simp 
    constructor
    · -- First direction: if (a, b) is a solution, it's in the finite set.
      rintro H

      have h2 : a ≤ 26 := by 
        omega 
      have h3 : b ≤ 90 := by
        omega 
      interval_cases a <;> omega 
    · -- Now, proving any pair in the finite set is in the solution set.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals 
        norm_num 
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try native_decide