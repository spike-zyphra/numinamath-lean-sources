import Mathlib

theorem algebra_166636 :
    {(a, b) : ℤ × ℤ | a > 0 ∧ b > 0 ∧ (a + b + 3)^2 = 4 * (a^2 + b^2)}.ncard = 2 := by
  have h1 : {(a, b) : ℤ × ℤ | a > 0 ∧ b > 0 ∧ (a + b + 3)^2 = 4 * (a^2 + b^2)} = {(3, 4), (4, 3)} := by
    ext ⟨a, b⟩
    simp
    constructor
    · -- Forward implication: if (a,b) is in the set, then (a,b)=(3,4) or (4,3)
      rintro ⟨ha, hb, heq⟩
      have h2 : a ≤ 5 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 3)]
      have h3 : b ≤ 5 := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 3)]
      interval_cases a <;> interval_cases b <;> omega
    · -- Backward implication: (3,4) and (4,3) satisfy the equation
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
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
  rw [Set.ncard_pair (by norm_num)]
  all_goals norm_num