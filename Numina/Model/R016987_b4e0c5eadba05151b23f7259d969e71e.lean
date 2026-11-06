import Mathlib

theorem algebra_11366 :
    IsLeast {x : ℝ | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ x = a / b + b / c + c / a} 3 := by
  constructor
  · -- Show 3 is in the set
    use 1, 1, 1
    norm_num
  · -- Show 3 is the least element in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, hx⟩
    have h1 : a / b + b / c + c / a ≥ 3 := by
      have h2 : a / b + b / c + c / a - 3 ≥ 0 := by
        have h3 : a / b + b / c + c / a - 3 = (a ^ 2 * c + b ^ 2 * a + c ^ 2 * b - 3 * a * b * c) / (a * b * c) := by
          field_simp
          ring
        have h4 : a ^ 2 * c + b ^ 2 * a + c ^ 2 * b ≥ 3 * a * b * c := by
          nlinarith [sq_nonneg (a * c - b * a), sq_nonneg (b * a - c * b), sq_nonneg (c * b - a * c),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
        have h5 : (a ^ 2 * c + b ^ 2 * a + c ^ 2 * b - 3 * a * b * c) / (a * b * c) ≥ 0 := by
          have h6 : a * b * c > 0 := by
            positivity
          apply div_nonneg
          linarith [h4]
          all_goals positivity
        linarith [h3, h5]
      linarith
    linarith [h1, hx]