import Mathlib

theorem number_theory_131613 :
    {(x, y) : ℤ × ℤ | 4 * x ^ 2 + 7 * y ^ 2 = 1600}.encard = 6 ∧
    {(x, y) : ℤ × ℤ | 4 * x ^ 2 + 7 * y ^ 2 = 1600} = {(20, 0), (15, 10), (-15, 10), (-20, 0), (15, -10), (-15, -10)} := by
  have h1 : {(x, y) : ℤ × ℤ | 4 * x ^ 2 + 7 * y ^ 2 = 1600} = {(20, 0), (15, 10), (-15, 10), (-20, 0), (15, -10), (-15, -10)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Forward
      rintro H
      have h2 : x ≤ 20 := by nlinarith [sq_nonneg (x - 20), sq_nonneg (y * 1)]
      have h3 : x ≥ -20 := by nlinarith [sq_nonneg (x + 20), sq_nonneg (y * 1)]
      have h4 : y ≤ 15 := by nlinarith [sq_nonneg (y - 15), sq_nonneg (x * 1)]
      have h5 : y ≥ -15 := by nlinarith [sq_nonneg (y + 15), sq_nonneg (x * 1)]
      interval_cases x <;> interval_cases y
      <;> omega
    · -- Backward
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals
      norm_num
  have h2 : {(x, y) : ℤ × ℤ | 4 * x ^ 2 + 7 * y ^ 2 = 1600}.encard = 6 := by
    rw [h1]
    rw [Set.encard]
    simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
    <;> try { native_decide }
  constructor
  · exact h2
  · exact h1