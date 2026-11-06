import Mathlib

theorem algebra_258910 (a: ℝ) : (∃ (b c : ℝ), a^2 - b * c - 8 * a + 7 = 0 ∧ b^2 + c^2 + b * c - 6 * a + 6 = 0) ↔ 1 ≤ a ∧ a ≤ 9 := by
  constructor
  · -- Assume (∃ (b c : ℝ), a^2 - b * c - 8 * a + 7 = 0 ∧ b^2 + c^2 + b * c - 6 * a + 6 = 0), prove 1 ≤ a ∧ a ≤ 9
    rintro ⟨b, c, h1, h2⟩
    have h3 : b * c = a^2 - 8 * a + 7 := by 
      linarith
    have h4 : b^2 + c^2 + b * c = 6 * a - 6 := by
      linarith
    have h5 : (b + c) ^ 2 = (a - 1) ^ 2 := by
      have eq1 : (b + c) ^ 2 = b^2 + c^2 + 2 * (b * c) := by
        ring
      rw [eq1]
      have eq2 : b^2 + c^2 = (6 * a - 6) - (b * c) := by
        linarith
      rw [eq2, h3]
      all_goals
      nlinarith 
    have h8 : b + c = (a - 1) ∨ b + c = - (a - 1) := by 
      have h9 : (b + c) ^ 2 - (a - 1) ^ 2 = 0 := by 
        nlinarith [h5]
      have h10 : (b + c - (a - 1)) * (b + c + (a - 1)) = 0 := by
        nlinarith 
      cases' (mul_eq_zero.mp h10) with h11 h12
      · -- Case b + c - (a - 1) = 0
        left 
        linarith 
      · -- Case b + c + (a - 1) = 0
        right 
        linarith 
    cases h8 with
    | inl h9 =>
      have h10 : (b - c) ^ 2 ≥ 0 := by 
        apply sq_nonneg
      have h11 : (b - c) ^ 2 = (b + c) ^ 2 - 4 * (b * c) := by 
        ring
      rw [h11] at h10 
      rw [h9, h3] at h10 
      constructor 
      · -- 1 ≤ a 
        nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 9)]
      · -- a ≤ 9 
        nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 9)]
    | inr h9 =>
      have h10 : (b - c) ^ 2 ≥ 0 := by 
        apply sq_nonneg 
      have h11 : (b - c) ^ 2 = (b + c) ^ 2 - 4 * (b * c) := by 
        ring 
      rw [h11] at h10 
      rw [h9, h3] at h10
      constructor 
      · -- 1 ≤ a 
        nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 9)]
      · -- a ≤ 9 
        nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 9)]
  · -- Assume 1 ≤ a ∧ a ≤ 9, prove (∃ (b c : ℝ), a^2 - b * c - 8 * a + 7 = 0 ∧ b^2 + c^2 + b * c - 6 * a + 6 = 0)
    rintro ⟨ha1, ha2⟩
    use ( (a - 1) + Real.sqrt ( (a - 1) ^ 2 - 4 * (a^2 - 8 * a + 7) ) ) / 2, 
          ( (a - 1) - Real.sqrt ( (a - 1) ^ 2 - 4 * (a^2 - 8 * a + 7) ) ) / 2 
    constructor 
    · -- Check first equation: a^2 - b * c - 8 * a + 7 = 0 
      nlinarith [Real.sqrt_nonneg ( (a - 1) ^ 2 - 4 * (a^2 - 8 * a + 7) ), Real.sq_sqrt (show (a - 1) ^ 2 - 4 * (a^2 - 8 * a + 7) ≥ 0 by nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 9)] ) ]
    · -- Check second equation: b^2 + c^2 + b * c - 6 * a + 6 = 0 
      nlinarith [Real.sqrt_nonneg ( (a - 1) ^ 2 - 4 * (a^2 - 8 * a + 7) ), Real.sq_sqrt (show (a - 1) ^ 2 - 4 * (a^2 - 8 * a + 7) ≥ 0 by nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 9)] ) ]