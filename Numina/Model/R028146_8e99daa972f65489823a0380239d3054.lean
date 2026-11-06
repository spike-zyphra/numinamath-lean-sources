import Mathlib

theorem algebra_15304 : {x : ℝ | 0 ≤ (x - 10 * x ^ 2 + 25 * x ^ 3) / (8 - x ^ 3) ∧ 8 - x ^ 3 ≠ 0} = Set.Ico 0 2 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ico]
  constructor
  · -- Assume 0 ≤ (x - 10 * x^2 + 25 * x^3) / (8 - x^3) ∧ 8 - x^3 ≠ 0
    rintro ⟨h1, h2⟩
    by_cases h5 : 8 - x^3 > 0
    · -- If 8 - x^3 > 0, then Numerator ≥ 0
      have h6 : 0 ≤ x - 10 * x ^ 2 + 25 * x ^ 3 := by
        have h7 : (x - 10 * x ^ 2 + 25 * x ^ 3) / (8 - x ^ 3) ≥ 0 := by linarith
        apply div_nonneg_iff.mp at h7
        cases h7 with
        | inl h8 =>
          linarith
        | inr h8 =>
          linarith
      have h7 : x < 2 := by
        nlinarith
      constructor
      · -- Show that 0 ≤ x
        nlinarith
      · -- Show that x < 2
        linarith
    · -- If 8 - x^3 ≤ 0, then because h4 : 8 - x^3 ≠ 0, we have 8 - x^3 < 0
      have h8 : 8 - x ^ 3 < 0 := by
        by_contra h8
        push_neg at h8
        have : 8 - x ^ 3 = 0 := by linarith
        contradiction
      have h9 : x - 10 * x ^ 2 + 25 * x ^ 3 ≤ 0 := by
        have h7 : (x - 10 * x ^ 2 + 25 * x ^ 3) / (8 - x ^ 3) ≥ 0 := by linarith
        apply div_nonneg_iff.mp at h7
        cases h7 with
        | inl h8 =>
          linarith
        | inr h8 =>
          linarith
      have h10 : x ^ 3 > 8 := by nlinarith
      have h11 : x > 2 := by
        have h12 : x ^ 3 > 8 := h10
        have h13 : x > 0 := by nlinarith
        have h14 : x > 2 := by
          by_contra h
          push_neg at h
          have : x ≤ 2 := by nlinarith
          nlinarith [sq_nonneg (x - 2), sq_nonneg (x ^ 2 + 4)]
        linarith
      have h12 : x - 10 * x ^ 2 + 25 * x ^ 3 > 0 := by
        nlinarith [sq_nonneg (5 * x - 1), sq_nonneg (x - 1 / 5), sq_nonneg (x - 2)]
      linarith
  · -- Assume x ∈ [0, 2)
    rintro ⟨hx0, hx2⟩
    have h1 : 0 < 8 - x^3 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 2)]
    have h2 : 0 ≤ x - 10 * x ^ 2 + 25 * x ^ 3 := by
      nlinarith [sq_nonneg (5 * x - 1), sq_nonneg (x - 1 / 5), sq_nonneg (x - 2)]
    constructor
    · -- Show that 0 ≤ (x - 10 * x ^ 2 + 25 * x ^ 3) / (8 - x ^ 3)
      apply div_nonneg
      all_goals linarith
    · -- Show that 8 - x ^ 3 ≠ 0
      by_contra h
      nlinarith [sq_nonneg (x - 2)]