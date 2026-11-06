import Mathlib

/- If positive real numbers $a$, $b$ satisfy $ab=2a+b$, then the minimum value of $a+2b$ is ___          ___. -/
theorem algebra_8343 : IsLeast {x : ℝ | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a * b = 2 * a + b ∧ x = a + 2 * b} 9 := by
  constructor
  · -- Show 9 is in the set
    use 3, 3
    norm_num
  · -- Show 9 is the least element in the set
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h, hx⟩
    nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 3), 
      sq_nonneg (a * b - 9), mul_pos ha hb, 
      sq_nonneg (a - 2 * b), sq_nonneg (a - 2 * b / 3), sq_nonneg (a - 1), sq_nonneg (b - 2)]