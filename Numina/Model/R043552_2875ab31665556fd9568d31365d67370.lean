import Mathlib

theorem algebra_20957 :
    IsGreatest { x | ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ √a - √b = 20 ∧ x = a - 5 * b } 500 := by
  constructor
  · -- Show that 500 is achievable
    use 625, 25
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- Show that sqrt(625) - sqrt(25) = 20
      have h1 : Real.sqrt (625 : ℝ) = 25 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h2 : Real.sqrt (25 : ℝ) = 5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1, h2]
      all_goals norm_num
    · -- Show that 500 = 625 - 5 * 25
      norm_num
  · -- Show that 500 is the greatest element in the set
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h1, hx⟩
    have h2 : Real.sqrt a = Real.sqrt b + 20 := by
      linarith
    have h3 : a = (Real.sqrt a) ^ 2 := by
      rw [Real.sq_sqrt]
      linarith
    have h4 : b = (Real.sqrt b) ^ 2 := by
      rw [Real.sq_sqrt]
      linarith
    have h5 : a - 5 * b ≤ 500 := by
      have h6 : Real.sqrt a = Real.sqrt b + 20 := h2
      have h7 : a = (Real.sqrt a) ^ 2 := h3
      have h8 : b = (Real.sqrt b) ^ 2 := h4
      have h9 : a - 5 * b = -4 * (Real.sqrt b) ^ 2 + 40 * (Real.sqrt b) + 400 := by
        have h10 : (Real.sqrt a) ^ 2 = (Real.sqrt b + 20) ^ 2 := by
          rw [h6]
        nlinarith [Real.sqrt_nonneg (a), Real.sqrt_nonneg (b)]
      nlinarith [sq_nonneg (Real.sqrt b - 5), Real.sqrt_nonneg (b)]
    linarith [h5, hx]