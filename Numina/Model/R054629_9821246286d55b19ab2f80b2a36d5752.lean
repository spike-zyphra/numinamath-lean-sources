import Mathlib

theorem number_theory_107118 : {p : ℤ × ℤ | p.1 ≥ 3 ∧ p.2 ≥ 17 ∧ p.1 ≤ 48 ∧ p.2 ≤ 281 ∧ (p.1 - 3) * (281 - 17) = (p.2 - 17) * (48 - 3)}.ncard = 4 := by
  have h₁ : {p : ℤ × ℤ | p.1 ≥ 3 ∧ p.2 ≥ 17 ∧ p.1 ≤ 48 ∧ p.2 ≤ 281 ∧ (p.1 - 3) * (281 - 17) = (p.2 - 17) * (48 - 3)} = {(3, 17), (18, 105), (33, 193), (48, 281)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- First, we show that if $(x, y)$ satisfies all the conditions, then $(x, y) \in \{(3, 17), (18, 105), (33, 193), (48, 281)\}$.
      rintro ⟨hx1, hy1, hx2, hy2, hline⟩
      have h1 : x ≥ 3 := hx1
      have h2 : y ≥ 17 := hy1
      have h3 : x ≤ 48 := hx2
      have h4 : y ≤ 281 := hy2
      interval_cases x <;> omega 
    · -- Next, we show that if $(x, y) \in \{(3, 17), (18, 105), (33, 193), (48, 281)\}$, then it satisfies all the conditions.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
      · constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
      · constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
      · constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
  rw [h₁]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }