import Mathlib

theorem number_theory_16037 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x * y = 2007}.encard = 6 := by
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x * y = 2007} = {(1, 2007), (3, 669), (9, 223), (223, 9), (669, 3), (2007, 1)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · 
      rintro ⟨hx, hy, h_eq⟩
      have h2 : x ∣ 2007 := by
        use y
        linarith 
      have h3 : x ≤ 2007 := by 
        apply Nat.le_of_dvd (by linarith)
        use y
        linarith 
      interval_cases x <;> omega 
    · 
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals 
        constructor <;> norm_num 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { native_decide }