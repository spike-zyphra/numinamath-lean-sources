import Mathlib

theorem algebra_285945 :
  {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ (x - 6) * (y - 6) = 18} =
  {(9, 12), (12, 9), (8, 15), (15, 8), (7, 24), (24, 7)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume ⟨x, y⟩ is in the left side. Then it must satisfy the conditions.
    rintro ⟨hx, hy, h⟩
    have h1 : x ≤ 24 := by
      by_contra h2
      push_neg at h2
      have h2' : x - 6 ≥ 19 := by 
        omega 
      by_cases h3 : y - 6 > 0
      · -- Suppose y - 6 > 0.
        nlinarith 
      · -- Suppose y - 6 ≤ 0. Then y - 6 = 0.
        have h4 : y - 6 = 0 := by
          have h4 : y - 6 ≤ 0 := by nlinarith
          omega 
        rw [h4] at h 
        nlinarith
    have h2 : y ≤ 24 := by
      by_contra h3
      push_neg at h3
      have h3' : y - 6 ≥ 19 := by 
        omega 
      by_cases h4 : x - 6 > 0
      · -- Suppose x - 6 > 0.
        nlinarith 
      · -- Suppose x - 6 ≤ 0. Then x - 6 = 0.
        have h5 : x - 6 = 0 := by
          have h5 : x - 6 ≤ 0 := by nlinarith
          omega 
        rw [h5] at h 
        nlinarith
    interval_cases x <;> interval_cases y 
    <;> omega 
  · -- Assume ⟨x, y⟩ is in the right side.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check (9, 12)
      constructor
      · norm_num
      constructor
      · norm_num
      all_goals norm_num
    · -- Check (12, 9)
      constructor
      · norm_num
      constructor
      · norm_num
      all_goals norm_num
    · -- Check (8, 15)
      constructor
      · norm_num
      constructor
      · norm_num
      all_goals norm_num
    · -- Check (15, 8)
      constructor
      · norm_num
      constructor
      · norm_num
      all_goals norm_num
    · -- Check (7, 24)
      constructor
      · norm_num
      constructor
      · norm_num
      all_goals norm_num
    · -- Check (24, 7)
      constructor
      · norm_num
      constructor
      · norm_num
      all_goals norm_num