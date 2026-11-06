import Mathlib

open Real

theorem algebra_11780 :
    IsLeast {x : ℝ | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ x = (a + b) / c + (a + c) / b + (b + c) / a} 6 := by 
  constructor 
  · -- Show 6 belongs to the set
    use 1, 1, 1
    norm_num
  · -- Suppose x ∈ s, prove that 6 ≤ x
    intro x hx
    rcases hx with ⟨a, b, c, a1, b1, c1, hx⟩
    have h1 : (a + b) / c + (a + c) / b + (b + c) / a ≥ 6 := by 
      have h2 : (a + b) / c + (a + c) / b + (b + c) / a - 6 ≥ 0 := by
        have h3 : (a + b) / c + (a + c) / b + (b + c) / a - 6 = (a * b * (a + b) + a * c * (a + c) + b * c * (b + c) - 6 * a * b * c) / (a * b * c) := by
          field_simp
          ring
        rw [h3]
        have h4 : a * b * (a + b) + a * c * (a + c) + b * c * (b + c) - 6 * a * b * c ≥ 0 := by
          nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (b * a - b * c), sq_nonneg (c * a - c * b), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_pos a1 b1, mul_pos b1 c1, mul_pos a1 c1]
        have h4' : a * b * c > 0 := by
          positivity
        have h5 : (a * b * (a + b) + a * c * (a + c) + b * c * (b + c) - 6 * a * b * c) ≥ 0 := by linarith [h4]
        have h6 : (a * b * (a + b) + a * c * (a + c) + b * c * (b + c) - 6 * a * b * c) / (a * b * c) ≥ 0 := by 
          apply div_nonneg 
          linarith 
          all_goals 
            positivity
        linarith 
      linarith
    linarith [hx, h1]