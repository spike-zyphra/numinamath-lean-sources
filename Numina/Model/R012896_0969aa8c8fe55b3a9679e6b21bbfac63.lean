import Mathlib

theorem algebra_6725 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 5 * x + 6 * y = 268}.encard = 9 := by
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 5 * x + 6 * y = 268} = 
          {(50, 3), (44, 8), (38, 13), (32, 18), (26, 23), (20, 28), (14, 33), (8, 38), (2, 43)} := by
    ext ⟨x, y⟩ 
    simp 
    constructor 
    · -- Assume $x>0 \land y>0 \land 5x+6y=268$, prove $(x,y) \in \{ \ldots \}$.
      rintro ⟨hx, hy, heq⟩ 
      have h2 : x ≤ 53 := by
        omega 
      have h3 : y ≤ 44 := by 
        omega 
      interval_cases x <;> try { 
        omega 
      } 
    · -- Assume $(x,y) \in \{ \ldots \}$, prove $x>0 \land y>0 \land 5x+6y=268$.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) 
      · -- (50, 3)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
      · -- (44, 8)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
      · -- (38, 13)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
      · -- (32, 18)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
      · -- (26, 23)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
      · -- (20, 28)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
      · -- (14, 33)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
      · -- (8, 38)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
      · -- (2, 43)
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try aesop
  all_goals try { native_decide }