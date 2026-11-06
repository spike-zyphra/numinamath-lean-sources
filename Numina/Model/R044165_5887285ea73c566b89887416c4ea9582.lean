import Mathlib

theorem algebra_316266 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 2 * (x + y) = x * y + 7}.ncard = 2 := by
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 2 * (x + y) = x * y + 7} = {(1, 5), (5, 1)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Assume ⟨x, y⟩ is a positive integer solution.
      rintro ⟨hx, hy, h⟩
      have h2 : x ≤ 6 := by
        by_contra h2
        push_neg at h2
        have h3 : y ≤ 3 := by
          nlinarith [show x * y ≥ 7 * y by nlinarith]
        interval_cases y <;> nlinarith
      have h3 : y ≤ 6 := by
        by_contra h3
        push_neg at h3
        have h4 : x ≤ 3 := by
          nlinarith [show x * y ≥ x * 7 by nlinarith]
        interval_cases x <;> nlinarith
      interval_cases x <;> interval_cases y <;> omega
    · -- Show that (1,5) and (5,1) satisfy all constraints.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check (1, 5)
        constructor
        · norm_num -- 1 > 0
        constructor
        · norm_num -- 5 > 0
        · norm_num -- 2 * (1 + 5) = 1 * 5 + 7
      · -- Check (5, 1)
        constructor
        · norm_num -- 5 > 0
        constructor
        · norm_num -- 1 > 0
        · norm_num -- 2 * (5 + 1) = 5 * 1 + 7
  rw [h1]
  rw [Set.ncard_pair]
  all_goals norm_num