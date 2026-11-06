import Mathlib

theorem algebra_44 :
    IsGreatest {x : ℝ | ∃ a b c, x = (a - b)^2 + (b - c)^2 + (c - a)^2 ∧ a^2 + b^2 + c^2 = 9} 27 := by 
  constructor
  · -- Show that 27 is in the set.
    use (3 * Real.sqrt 2 / 2), (-3 * Real.sqrt 2 / 2), 0
    constructor
    · -- Show the algebraic expression equals 27
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)
      nlinarith [Real.sqrt_nonneg 2, h1]
    · -- Show a^2 + b^2 + c^2 = 9
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)
      nlinarith [Real.sqrt_nonneg 2, h1]
  · -- Show that 27 is the greatest element in the set
    intro x hx
    rcases hx with ⟨a, b, c, h1, h2⟩
    -- Show algebraic transformation
    have h3 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 2 * (a^2 + b^2 + c^2) - 2 * (a * b + b * c + c * a) := by
      ring
    rw [h3] at h1
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]