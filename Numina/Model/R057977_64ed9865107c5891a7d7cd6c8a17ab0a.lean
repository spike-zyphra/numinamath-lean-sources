import Mathlib

theorem inequalities_103772 (x : ℝ) :
    ∃ a : ℝ, -1 ≤ a ∧ a ≤ 2 ∧ (2 - a) * x ^ 3 + (1 - 2 * a) * x ^ 2 - 6 * x +
      (5 + 4 * a - a ^ 2) < 0 ↔ x < -2 ∨ (0 < x ∧ x < 1) ∨ (1 < x) := by

  by_cases h : 1 < x
  · -- Suppose 1 < x
    use 2
    constructor
    · -- Prove implication (→)
      intro ⟨h₁, h₂, h₃⟩
      right
      right
      linarith
    · -- Prove implication (←)
      rintro (h | ⟨h₁, h₂⟩ | h)
      · -- Case x < -2
        linarith
      · -- Case 0 < x ∧ x < 1
        linarith
      · -- Case 1 < x
        constructor
        · norm_num
        constructor
        · norm_num
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2)]
  · -- Suppose not 1 < x
    use -1
    constructor
    · -- Prove implication (→)
      rintro ⟨h₁, h₂, h₃⟩
      by_cases h4 : x < -2
      · left
        linarith
      · -- Case -2 ≤ x ≤ 1
        have h5 : 0 < x := by nlinarith [sq_nonneg (x), sq_nonneg (x - 1), sq_nonneg (x + 2)]
        have h6 : x < 1 := by nlinarith [sq_nonneg (x), sq_nonneg (x - 1), sq_nonneg (x + 2)]
        right
        left
        constructor <;> nlinarith
    · -- Prove implication (←)
      rintro (h | ⟨h₁, h₂⟩ | h)
      · -- Case x < -2
        constructor
        · norm_num
        constructor
        · norm_num
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 2), sq_nonneg (x - 0)]
      · -- Case 0 < x ∧ x < 1
        constructor
        · norm_num
        constructor
        · norm_num
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 2), sq_nonneg (x - 0)]
      · -- Case 1 < x
        exfalso
        linarith