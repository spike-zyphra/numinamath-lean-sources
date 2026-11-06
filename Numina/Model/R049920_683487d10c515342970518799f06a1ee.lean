import Mathlib

open Real Set

theorem inequalities_126211 :
    IsLeast {x | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 8 ∧ x = a + b + c} 6 := by
  constructor
  · -- Show 6 is achievable, by setting a = b = c = 2.
    use 2, 2, 2
    norm_num
  · -- Prove that 6 is the least value in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, hprod, hx⟩
    
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]