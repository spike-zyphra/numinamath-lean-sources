import Mathlib

theorem algebra_5506 :
  IsLeast {x | ∃ a b c : ℝ, a ^ 2 + b ^ 2 + c ^ 2 = 1 ∧ x = a * b + a * c + b * c} (-1 / 2) := by
  constructor
  · -- Show $(-1/2) \in \set$
    use Real.sqrt 6 / 6, Real.sqrt 6 / 6, -Real.sqrt 6 / 3 
    constructor
    · -- Verify $a^2 + b^2 + c^2 = 1$ 
      have h2 : (Real.sqrt 6 : ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
      linarith [Real.sqrt_nonneg 6]
    · -- Verify $ab + ac + bc = -1/2$
      have h2 : (Real.sqrt 6 : ℝ) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 6]
  · -- Show $-1/2$ is the least element of the set
    intro x hx
    rcases hx with ⟨a, b, c, h1, h2⟩ 
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]