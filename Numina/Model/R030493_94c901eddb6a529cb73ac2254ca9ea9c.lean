import Mathlib

theorem algebra_319143 : {k : ℤ | ∃ x y : ℤ, y = x - 3 ∧ y = k * x + k}.encard = 6 := by
  have h1 : {k : ℤ | ∃ x y : ℤ, y = x - 3 ∧ y = k * x + k} = {0, 2, -1, 3, -3, 5} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume k ∈ {k : ℤ | ∃ x y : ℤ, y = x - 3 ∧ y = k * x + k}
      intro h
      rcases h with ⟨x, y, h1, h2⟩
      have h3 : x - 3 = k * x + k := by 
        linarith [h1, h2]
      have h8 : (1 - k) * x = k + 3 := by
        nlinarith 
      have h9 : k = 0 ∨ k = 2 ∨ k = -1 ∨ k = 3 ∨ k = -3 ∨ k = 5 := by
        have h10 : (1 - k) ∣ 4  := by
          have h13 : (1 - k) * (x + 1) = 4 := by
            nlinarith [h8]
          have h14 : (1 - k) ∣ 4 := by 
            use x + 1 
            all_goals linarith [h13]
          exact h14
        have h11 : (1 - k) ≤ 4  := by 
          apply Int.le_of_dvd (by norm_num) h10 
        have h12 : (1 - k) ≥ -4  := by 
          have h12 : -(1 - k) ∣ 4 := by
            exact Int.neg_dvd.2 h10 
          have h13 : -(1 - k) ≤ 4  := by 
            apply Int.le_of_dvd (by norm_num) h12 
          linarith 
        have h111 : k ≤ 5  := by 
          omega 
        have h112 : k ≥ -3  := by 
          omega 
        interval_cases k <;> try { tauto } 
      tauto 
    · -- Show that if k ∈ {0, 2, -1, 3, -3, 5}, then k is in the set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- k = 0
        refine ⟨3, 0, by norm_num, by norm_num⟩ 
      · -- k = 2
        refine ⟨-5, -8, by norm_num, by norm_num⟩ 
      · -- k = -1
        refine ⟨1, -2, by norm_num, by norm_num⟩ 
      · -- k = 3
        refine ⟨-3, -6, by norm_num, by norm_num⟩ 
      · -- k = -3
        refine ⟨0, -3, by norm_num, by norm_num⟩ 
      · -- k = 5
        refine ⟨-2, -5, by norm_num, by norm_num⟩ 
  rw [h1]
  rw [Set.encard]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> try { native_decide }