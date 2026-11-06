import Mathlib

theorem algebra_12143 (S : Finset (ℕ × ℕ)) (hS : ∀ x y : ℕ, (x, y) ∈ S ↔ x > 0 ∧ y > 0 ∧ x * y = 6 * (x + y)) :
    ∑ k ∈ S, (k.1 + k.2) = 290 := by
  have h1 : S = {(7, 42), (8, 24), (9, 18), (10, 15), (12, 12), (15, 10), (18, 9), (24, 8), (42, 7)} := by
    ext ⟨x, y⟩
    simp [hS]
    constructor
    · -- Assume (x, y) ∈ S, so x > 0 ∧ y > 0 ∧ x * y = 6 * (x + y)
      rintro ⟨hx1, hy1, h_eq⟩
      have h2 : x ≤ 42 := by
        by_contra h
        push_neg at h
        have h3 : y < 7 := by
          nlinarith
        interval_cases y <;> try { 
          omega 
        }
      interval_cases x <;> omega
    · -- Show that (x, y) ∈ S, so x > 0 ∧ y > 0 ∧ x * y = 6 * (x + y)
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  native_decide