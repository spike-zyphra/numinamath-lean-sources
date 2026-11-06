import Mathlib

theorem algebra_313601 :
    {(x, y) : ℤ × ℤ | x^2 + x * y + 2 * y^2 = 29}.encard = 4 := by
  have h1 : {(x, y) : ℤ × ℤ | x^2 + x * y + 2 * y^2 = 29} = {(-1, 4), (-3, 4), (1, -4), (3, -4)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume $x^2 + x \cdot y + 2 \cdot y^2 = 29$; prove $(x, y) \in \{(-1, 4), (-3, 4), (1, -4), (3, -4)\}$.
      rintro H
      have h2 : y ≥ -4 := by
        nlinarith [sq_nonneg (x + y), sq_nonneg (y - 4), sq_nonneg (y + 4)]
      have h3 : y ≤ 4 := by
        nlinarith [sq_nonneg (x + y), sq_nonneg (y - 4), sq_nonneg (y + 4)]
      interval_cases y <;> try { 
        norm_num at H 
        all_goals 
          have : x ≤ 7 := by nlinarith 
          have : x ≥ -7 := by nlinarith 
          interval_cases x <;> norm_num at H ⊢ <;> tauto 
      }
      all_goals omega 
    · -- Assume $(x, y) \in \{(-1, 4), (-3, 4), (1, -4), (3, -4)\}$; prove $x^2 + x \cdot y + 2 \cdot y^2 = 29$.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals 
        norm_num 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> aesop