import Mathlib
theorem algebra_24048 : IsLeast {s | ∃ a b c d : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ (a + c) * (b + d) = a * c + b * d ∧
s = a / b + b / c + c / d + d / a} 8:= by
  constructor
  · -- Show that 8 is in the set
    use 2 + Real.sqrt 3, 1, 2 + Real.sqrt 3, 1
    constructor
    · -- Show 2 + Real.sqrt 3 > 0
      positivity
    constructor
    · -- Show 1 > 0
      positivity
    constructor
    · -- Show 2 + Real.sqrt 3 > 0
      positivity
    constructor
    · -- Show 1 > 0
      positivity
    constructor
    · -- Show $(2 + \sqrt{3} + (2 + \sqrt{3})) * (1 + 1) = (2 + \sqrt{3}) * (2 + \sqrt{3}) + 1 * 1$
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    · -- Show $8 = S$
      field_simp [(show (2 + Real.sqrt 3 : ℝ) ≠ 0 by positivity), (show (1 : ℝ) ≠ 0 by positivity)]
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  · -- Show that 8 is the minimum
    intro s hs
    rcases hs with ⟨a, b, c, d, ha, hb, hc, hd, h, heq⟩
    have h1 : 0 < a * b * c * d := by positivity
    have h2 : a ^ 2 * c * d + b ^ 2 * a * d + c ^ 2 * a * b + d ^ 2 * b * c ≥ 8 * (a * b * c * d) := by
      nlinarith [sq_nonneg (a * b - c * d), sq_nonneg (a * d - b * c), sq_nonneg (a - c), sq_nonneg (b - d),
                  sq_nonneg (a * d + b * c - a * b - c * d), sq_nonneg (a * d + b * c - a * c - b * d),
                  sq_nonneg (a * b + c * d - a * c - b * d), sq_nonneg (a * d - b * c),
                  mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, sq_nonneg (a * d + b * c - 2 * (a * b + c * d)), sq_nonneg ( (a + c) * (b + d) - 2 * (a * c + b * d) ) ]
    have h3 : a / b + b / c + c / d + d / a ≥ 8 := by
      have h4 : a / b + b / c + c / d + d / a - 8 ≥ 0 := by
        have h5 : a / b + b / c + c / d + d / a - 8 = (a ^ 2 * c * d + b ^ 2 * a * d + c ^ 2 * a * b + d ^ 2 * b * c - 8 * (a * b * c * d)) / (a * b * c * d) := by
          field_simp [hb.ne', hc.ne', ha.ne', hd.ne']
          ring
        rw [h5]
        apply div_nonneg
        linarith [h2]
        positivity
      linarith
    rw [heq]
    linarith [h3]