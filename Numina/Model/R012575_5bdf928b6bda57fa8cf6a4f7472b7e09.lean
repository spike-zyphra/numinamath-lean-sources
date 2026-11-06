import Mathlib

open BigOperators Real Set

lemma lemma_1 (a b : ℝ) (h : a^2 + 9 * b^2 ≠ 0) : (((3 * a * b - 6 * b + a * (1 - a))^2 + (9 * b^2 + 2 * a + 3 * b * (1 - a))^2) / (a^2 + 9 * b^2) = 4 + (1 - a + 3 * b)^2) := by
  have h1 : a^2 + 9 * b^2 ≠ 0 := h
  field_simp [h1]
  nlinarith [sq_nonneg (a - 3 * b), sq_nonneg (a + 3 * b), sq_nonneg (a - 1), sq_nonneg (b), sq_nonneg (a - 0 * b)]


theorem algebra_223689 :
  IsLeast {x | ∃ a b : ℝ, a > 0 ∧ b > 0 ∧
    x = ((3 * a * b - 6 * b + a * (1 - a))^2 +
          (9 * b^2 + 2 * a + 3 * b * (1 - a))^2) / (a^2 + 9 * b^2)} 4 := by
  constructor
  · -- First part: 4 is in the set.
    use 2
    use 1 / 3
    constructor
    · norm_num -- a > 0
    constructor
    · norm_num -- b > 0
    · -- Calculate the value
      norm_num [lemma_1]
  · -- Second part: 4 is the infimum.
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hx⟩
    -- First we need the expression is ≥ 4.
    have h1 : a^2 + 9 * b^2 ≠ 0 := by
      have h21 : a^2 > 0 := by nlinarith [sq_pos_of_pos ha]
      have h22 : 9 * b^2 > 0 := by nlinarith [sq_pos_of_pos hb]
      have h23 : a^2 + 9 * b^2 > 0 := by linarith
      linarith
    have eq1 : ((3 * a * b - 6 * b + a * (1 - a))^2 + (9 * b^2 + 2 * a + 3 * b * (1 - a))^2) / (a^2 + 9 * b^2) = 4 + (1 - a + 3 * b)^2 := by
      apply lemma_1 a b h1
    have h2 : 4 + (1 - a + 3 * b)^2 ≥ 4 := by
      nlinarith [sq_nonneg (1 - a + 3 * b)]
    linarith [eq1, h2, hx]