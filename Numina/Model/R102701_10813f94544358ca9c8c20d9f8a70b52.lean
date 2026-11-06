import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_240865 :
  IsLeast {x | ∃ a b c d : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ x =
    a / (b + c + d) + b / (c + d + a) + c / (a + b + d) + d / (a + b + c)} (4 / 3) := by
  constructor
  · -- Show that 4/3 is achievable, by setting all variables equal to 1
    use 1, 1, 1, 1
    norm_num
  · -- Show that 4/3 is a lower bound
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, hx⟩
    have h1 : a / (b + c + d) + b / (c + d + a) + c / (a + b + d) + d / (a + b + c) ≥ 4 / 3 := by
      have h2 : a / (b + c + d) + b / (c + d + a) + c / (a + b + d) + d / (a + b + c) - 4 / 3 ≥ 0 := by
        have h3 : a / (b + c + d) + b / (c + d + a) + c / (a + b + d) + d / (a + b + c) - 4 / 3 = 
          (a * (c + d + a) * (a + b + d) * (a + b + c) + 
           b * (b + c + d) * (a + b + d) * (a + b + c) + 
           c * (b + c + d) * (c + d + a) * (a + b + c) + 
           d * (b + c + d) * (c + d + a) * (a + b + d) - 
           (4 / 3) * (b + c + d) * (c + d + a) * (a + b + d) * (a + b + c)) / 
          ((b + c + d) * (c + d + a) * (a + b + d) * (a + b + c)) := by
          field_simp
          ring
        rw [h3]
        apply div_nonneg
        · -- The numerator is non-negative
          nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (a - d)), 
            sq_nonneg (b * (b - c)), sq_nonneg (b * (b - d)), sq_nonneg (c * (c - d)), 
            mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]
        · -- The denominator is positive
          positivity
      linarith
    linarith [hx, h1]