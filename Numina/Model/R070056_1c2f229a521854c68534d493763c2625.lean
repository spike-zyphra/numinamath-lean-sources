import Mathlib

theorem algebra_288996 :
    {(x, y) : ℕ × ℕ | 0 < x ∧ 0 < y ∧ x < y ∧ 2 * x + 3 * y = 80}.encard = 5 := by
  have h1 : {(x, y) : ℕ × ℕ | 0 < x ∧ 0 < y ∧ x < y ∧ 2 * x + 3 * y = 80} = 
    {(1, 26), (4, 24), (7, 22), (10, 20), (13, 18)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Forward direction: Show that all pairs (x, y) in the set are in the finite collection
      rintro ⟨hx, hy, hxy, heq⟩
      have h1 : y ≤ 26 := by omega
      interval_cases y <;> omega
    · -- Backward direction: Show that all pairs in the finite collection satisfy the conditions
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals 
        constructor
        · norm_num
        all_goals 
          norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }