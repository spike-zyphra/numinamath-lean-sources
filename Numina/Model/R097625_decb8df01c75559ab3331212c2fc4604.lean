import Mathlib

theorem number_theory_27333 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x + y + x * y = 2006} =
    {(2, 668), (668, 2), (8, 222), (222, 8)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Forward direction: if (x, y) satisfies the equation, then it's one of the listed pairs
    rintro ⟨hx, hy, h⟩
    have h1 : x ≤ 2006 := by
      nlinarith [h, mul_self_nonneg (x + 1), mul_self_nonneg (y + 1)]
    have h2 : y ≤ 2006 := by
      nlinarith [h, mul_self_nonneg (x + 1), mul_self_nonneg (y + 1)]
    interval_cases x <;> omega
  · -- Backward direction: if (x, y) is one of the listed pairs, then it satisfies the equation
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Verify (2, 668)
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Verify (668, 2)
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Verify (8, 222)
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Verify (222, 8)
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num