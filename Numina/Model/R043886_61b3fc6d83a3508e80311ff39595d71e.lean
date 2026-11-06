import Mathlib

open Real

theorem inequalities_103130 :
    IsGreatest {x | ∃ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a^2 + b^2 + c^2 + a * b * c ≤ 4 ∧ x = a + b + c + a * b * c} 4 := by 
  constructor
  · -- Show 4 is in the set
    use 1, 1, 1
    norm_num
  · -- Show 4 is greatest
    rintro x ⟨a, b, c, ha, hb, hc, h1, hx⟩
    have h2 : a + b + c + a * b * c ≤ 4 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
    linarith [hx, h2]