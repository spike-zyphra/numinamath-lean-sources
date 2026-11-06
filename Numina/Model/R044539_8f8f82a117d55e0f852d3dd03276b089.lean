import Mathlib

theorem algebra_605431 :
    IsLeast {x : ℝ | ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ (a + c) * (b + d) = a * c + b * d ∧ x = a / b + b / c + c / d + d / a} 8 := by

  constructor
  · -- First, we show 8 is in the set
    use 2 - Real.sqrt 3, 1, 2 - Real.sqrt 3, 1
    constructor
    · -- Show 0 < 2 - Real.sqrt 3
      have h1 : Real.sqrt 3 < 2 := by
        rw [Real.sqrt_lt] <;> norm_num
      nlinarith
    constructor
    · -- Show 0 < 1
      norm_num
    constructor
    · -- Show 0 < 2 - Real.sqrt 3
      have h1 : Real.sqrt 3 < 2 := by
        rw [Real.sqrt_lt] <;> norm_num
      nlinarith
    constructor
    · -- Show 0 < 1
      norm_num
    constructor
    · -- Show (a + c) * (b + d) = a * c + b * d
      ring_nf
      have h1 : Real.sqrt 3 > 0 := by
        positivity
      have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 - 1)]
    · -- Show 8 = a / b + b / c + c / d + d / a
      have h1 : Real.sqrt 3 > 0 := by
        positivity
      have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      field_simp [(show (2 - Real.sqrt 3 : ℝ) ≠ 0 by nlinarith [Real.sqrt_nonneg 3, h2]), (show (1 : ℝ) ≠ 0 by norm_num)]
      <;> nlinarith [Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3), sq_nonneg (Real.sqrt 3 - 1)]
  · -- Show no value less than 8 is in the set
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, h_eq, hx⟩
    have h1 : a / b + b / c + c / d + d / a ≥ 8 := by
      have h2 : (a + c) * (b + d) = a * c + b * d := h_eq
      have h3 : a / b + b / c + c / d + d / a - 8 ≥ 0 := by
        have h4 : a * b * c * d > 0 := by
          positivity
        have h5 : a / b + b / c + c / d + d / a - 8 = (a ^ 2 * c * d + b ^ 2 * a * d + c ^ 2 * a * b + d ^ 2 * b * c - 8 * a * b * c * d) / (a * b * c * d) := by
          field_simp
          ring
        have h6 : a ^ 2 * c * d + b ^ 2 * a * d + c ^ 2 * a * b + d ^ 2 * b * c - 8 * a * b * c * d ≥ 0 := by
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * d), sq_nonneg (c * d - d * a), sq_nonneg (d * a - a * b),
            sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a * b - c * d), sq_nonneg (b * c - a * d),
            mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]
        have h7 : (a ^ 2 * c * d + b ^ 2 * a * d + c ^ 2 * a * b + d ^ 2 * b * c - 8 * a * b * c * d) / (a * b * c * d) ≥ 0 := by
          apply div_nonneg
          linarith
          all_goals
            positivity
        linarith [h5, h7]
      linarith
    linarith [h1, hx]