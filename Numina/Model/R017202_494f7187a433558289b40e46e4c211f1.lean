import Mathlib

theorem algebra_290967 (a : ℝ) :
    ∃ x y, 0 ≤ 2 * x * y + a ∧ Real.sqrt (2 * x * y + a) = x + y + 17 ↔
    a ≥ -289 / 2 := by
  by_cases h : a ≥ -289 / 2
  · -- Assume a ≥ -289 / 2.
    have h3 : 0 ≤ a + 289 / 2 := by linarith
    use (-17 + Real.sqrt (289 + 2 * a)) / 2, (-17 - Real.sqrt (289 + 2 * a)) / 2
    constructor
    · -- Assume 0 ≤ 2 * x * y + a ∧ Real.sqrt (2 * x * y + a) = x + y + 17, prove a ≥ -289 / 2
      intro h
      rcases h with ⟨h1, h2⟩
      linarith
    · -- Assume a ≥ -289 / 2, prove 0 ≤ 2 * x * y + a ∧ Real.sqrt (2 * x * y + a) = x + y + 17
      intro ha
      have h4 : 0 ≤ 2 * ((-17 + Real.sqrt (289 + 2 * a)) / 2) * ((-17 - Real.sqrt (289 + 2 * a)) / 2) + a := by
        nlinarith [Real.sqrt_nonneg (289 + 2 * a), Real.sq_sqrt (show 0 ≤ (289 + 2 * a : ℝ) by linarith)]
      have h5 : Real.sqrt (2 * ((-17 + Real.sqrt (289 + 2 * a)) / 2) * ((-17 - Real.sqrt (289 + 2 * a)) / 2) + a) = ((-17 + Real.sqrt (289 + 2 * a)) / 2) + ((-17 - Real.sqrt (289 + 2 * a)) / 2) + 17 := by
        have h6 : (2 * ((-17 + Real.sqrt (289 + 2 * a)) / 2) * ((-17 - Real.sqrt (289 + 2 * a)) / 2) + a : ℝ) = 0 := by
          nlinarith [Real.sqrt_nonneg (289 + 2 * a), Real.sq_sqrt (show 0 ≤ (289 + 2 * a : ℝ) by linarith)]
        rw [h6]
        have h7 : ((-17 + Real.sqrt (289 + 2 * a)) / 2) + ((-17 - Real.sqrt (289 + 2 * a)) / 2) + 17 = (0 : ℝ) := by
          ring
        rw [h7]
        simp
      constructor
      · exact h4
      · exact h5
  · -- Case a < -289 / 2.
    push_neg at h
    use 0, 0
    constructor
    · -- Assume 0 ≤ 2 * 0 * 0 + a ∧ Real.sqrt (2 * 0 * 0 + a) = 0 + 0 + 17, prove a ≥ -289 / 2
      intro h
      rcases h with ⟨h1, h2⟩
      nlinarith [Real.sqrt_nonneg (a), Real.sq_sqrt (show 0 ≤ (a : ℝ) by nlinarith)]
    · -- Assume a ≥ -289 / 2, prove 0 ≤ 2 * 0 * 0 + a ∧ Real.sqrt (2 * 0 * 0 + a) = 0 + 0 + 17
      intro h
      exfalso
      linarith