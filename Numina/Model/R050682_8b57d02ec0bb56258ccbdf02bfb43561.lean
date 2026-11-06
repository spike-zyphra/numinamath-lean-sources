import Mathlib

theorem algebra_127259 :
    IsLeast {x | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ 20 * a * b = 13 * a + 14 * b ∧ x = a * b} 1.82 := by
  constructor
  · -- Let's prove 1.82 is in the set
    use (7 / 5 : ℝ), (13 / 10 : ℝ)
    constructor
    · norm_num -- Show a > 0
    constructor
    · norm_num -- Show b > 0
    constructor
    · norm_num -- Show 20ab = 13a + 14b
    · norm_num -- Show 1.82 = a * b
  · -- Let's prove that 1.82 is a lower bound
    rintro x ⟨a, b, ha, hb, heq, hxy⟩
    have h1 : a * b ≥ 91 / 50 := by
      nlinarith [sq_nonneg (a - 7 / 5), sq_nonneg (b - 13 / 10), sq_nonneg (a * 20 - 14 * 24), sq_nonneg (b * 20 - 13 * 24), sq_nonneg (a * b - 91 / 50), sq_nonneg (a * b * 100 - 182 / 1), mul_pos ha hb, mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith)]
    rw [hxy]
    norm_num at h1 ⊢
    linarith