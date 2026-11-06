import Mathlib

theorem number_theory_289460 :
    Set.ncard {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ 20 * p.1 + 21 * p.2 = 2021} = 5 := by 
  have h1 : {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ 20 * p.1 + 21 * p.2 = 2021} = {(16, 81), (37, 61), (58, 41), (79, 21), (100, 1)} := by
    ext ⟨a, b⟩
    simp 
    constructor 
    · -- Assume (a, b) is in the left side 
      rintro ⟨ha, hb, h_eq⟩ 
      have h2 : a ≤ 101 := by omega 
      have h3 : b ≤ 96 := by omega 
      interval_cases a <;> omega 
    · -- Assume (a, b) is in the right side 
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals 
        constructor 
        · norm_num 
        all_goals 
          constructor 
          · norm_num 
          · norm_num 
  rw [h1] 
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.card_insert_of_not_mem, Finset.card_singleton]
  <;> try native_decide