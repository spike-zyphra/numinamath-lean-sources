import Mathlib

theorem algebra_23630 (a b : ℤ) :
7 * a + 14 * b = 5 * a^2 + 5 * a * b + 5 * b^2 
↔
(a = -1 ∧ b = 3) ∨ (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 2) := by 
  constructor
  · -- Assume the equation, prove the disjunction 
    intro h 
    have h1 : a ≤ 10 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - 1), sq_nonneg (b - 2)]
    have h2 : a ≥ -10 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a +1), sq_nonneg (b - 3)]
    have h3 : b ≤ 10 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (b - 3), sq_nonneg (a +1)]
    have h4 : b ≥ -10 := by 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a +1), sq_nonneg (b - 3)]
    interval_cases a <;> interval_cases b 
      <;> omega
  · -- Assume the disjunction, prove the equation 
    rintro (h | h | h)
    · -- Case where (a,b) = (-1,3)
      rcases h with ⟨ha, hb⟩ 
      rw [ha, hb] 
      all_goals norm_num 
    · -- Case where (a,b) = (0,0)
      rcases h with ⟨ha, hb⟩ 
      rw [ha, hb] 
      all_goals norm_num 
    · -- Case where (a,b) = (1,2)
      rcases h with ⟨ha, hb⟩ 
      rw [ha, hb] 
      all_goals norm_num