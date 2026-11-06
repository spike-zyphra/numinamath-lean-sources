import Mathlib

theorem inequalities_563 :
    Set.ncard {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 4 * x + 5 * y < 20} = 6 := by 
  have h : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 4 * x + 5 * y < 20} = {(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (3, 1)} := by
    ext ⟨x, y⟩
    simp 
    constructor
    · rintro ⟨hx1, hy1, hineq⟩
      have h1 : x ≤ 4 := by 
        omega 
      have h2 : y ≤ 3 := by 
        omega 
      interval_cases x <;> interval_cases y 
      <;> omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals 
        simp_all 
  rw [h] 
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> rfl