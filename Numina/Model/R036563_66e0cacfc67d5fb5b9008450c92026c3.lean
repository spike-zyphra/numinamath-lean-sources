import Mathlib

open Real Set

theorem algebra_20532 :
    IsLeast {x : ℝ | ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a + b + c + d = 1 ∧ x = 1 / a + 1 / b + 4 / c + 16 / d} 64 := by
  constructor
  · -- Show 64 is in the set.
    use 1 / 8, 1 / 8, 1 / 4, 1 / 2
    norm_num
  · -- Show 64 is the smallest element.
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, h_eq, hx⟩
    have h1 : 1 / a + 1 / b + 4 / c + 16 / d ≥ 64 := by
      have h3 : 1 / a + 1 / b + 4 / c + 16 / d - 64 ≥ 0 := by
        have h4 : a * b * c * d > 0 := by positivity
        have h6 : (1 / a + 1 / b + 4 / c + 16 / d - 64) = ( (b * c * d) + (a * c * d) + 4 * (a * b * d) + 16 * (a * b * c) - 64 * (a * b * c * d) ) / (a * b * c * d) := by 
          field_simp 
          ring
        rw [h6]
        apply div_nonneg
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c / 2), sq_nonneg (a - d / 4), 
                  sq_nonneg (b - c / 2), sq_nonneg (b - d / 4), 
                  sq_nonneg (c - d / 2), 
                  sq_nonneg (a + b - c - d), sq_nonneg (c - 2 * a), sq_nonneg (d - 4 * a), 
                  mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd 
                ]
        positivity
      linarith
    linarith [hx, h1]