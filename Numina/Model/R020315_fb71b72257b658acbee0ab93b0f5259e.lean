import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_301914 :
  IsGreatest {x | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 + c^2 = 1 ∧ x = a^2 * b * c + a * b^2 * c + a * b * c^2} (1 / 3) := by
  constructor
  · -- Show 1/3 is in the set
    use Real.sqrt (1 / 3), Real.sqrt (1 / 3), Real.sqrt (1 / 3)
    constructor
    · -- Show a > 0
      positivity
    constructor
    · -- Show b > 0
      positivity
    constructor
    · -- Show c > 0
      positivity
    constructor
    · -- Show a^2 + b^2 + c^2 = 1
      have h1 : (Real.sqrt (1 / 3) : ℝ) ^2 = 1 / 3 := Real.sq_sqrt (by linarith)
      nlinarith [h1]
    · -- Show 1/3 = s
      have h1 : (Real.sqrt (1 / 3) : ℝ) ^2 = 1 / 3 := Real.sq_sqrt (by linarith)
      have h4 : (Real.sqrt (1 / 3) : ℝ) ^4 = (1 / 9) := by
        calc
          (Real.sqrt (1 / 3) : ℝ) ^4 = ((Real.sqrt (1 / 3) : ℝ) ^2) ^2 := by ring
          _ = (1 / 3) ^2 := by rw [h1]
          _ = (1 / 9) := by norm_num
      nlinarith [h1, h4]
  · -- Show 1/3 is greatest in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, hx⟩
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              sq_nonneg (a * b - b * c), sq_nonneg (a * b - a * c), sq_nonneg (a * c - b * c),
              mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
            ]