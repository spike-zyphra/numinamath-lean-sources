import Mathlib

theorem algebra_309850 (S : Finset (ℕ × ℕ)) (hS : ∀ x y, (x, y) ∈ S ↔ x > 0 ∧ y > 0 ∧ x * y = 6 * (x + y)) :
    ∑ x in S, (x.1 + x.2) = 290 := by
  have h1 : S = {(7, 42), (8, 24), (9, 18), (10, 15), (12, 12), (15, 10), (18, 9), (24, 8), (42, 7)} := by
    ext ⟨x, y⟩
    simp [hS]
    constructor
    · -- Assume h : (x, y) ∈ S
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
    · -- Show (x, y) ∈ S
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Show (7, 42) ∈ S
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Show (8, 24) ∈ S
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Show (9, 18) ∈ S
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Show (10, 15) ∈ S
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Show (12, 12) ∈ S
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Show (15, 10) ∈ S
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Show (18, 9) ∈ S
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Show (24, 8) ∈ S
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Show (42, 7) ∈ S
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  native_decide