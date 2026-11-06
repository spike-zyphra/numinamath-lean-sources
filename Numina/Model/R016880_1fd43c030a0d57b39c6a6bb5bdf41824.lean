import Mathlib

theorem algebra_247734 (S : Finset (ℕ × ℕ)) (hS : ∀ x y : ℕ, (x, y) ∈ S ↔ x > 0 ∧ y > 0 ∧ x * y = 6 * (x + y)) :
    ∑ x in S, (x.1 + x.2) = 290 := by 
  have h1 : S = {(7, 42), (8, 24), (9, 18), (10, 15), (12, 12), (15, 10), (18, 9), (24, 8), (42, 7)} := by 
    ext ⟨x, y⟩
    simp [hS]
    constructor
    · -- Assume x * y = 6 * (x + y) with x, y > 0, prove (x, y) ∈ {(7, 42), ..., (42, 7)}
      rintro ⟨hx, hy, h_eq⟩
      have h2 : x ≤ 42 := by
        by_contra h
        push_neg at h
        have h3 : y ≤ 6 := by
          nlinarith
        interval_cases y <;> omega
      have h3 : y ≤ 42 := by
        by_contra h
        push_neg at h
        have h4 : x ≤ 6 := by
          nlinarith
        interval_cases x <;> omega
      interval_cases x <;> omega 
    · -- Assume (x, y) ∈ {(7, 42), ..., (42, 7)}, prove x * y = 6 * (x + y) with x, y > 0
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num 
  rw [h1]
  native_decide