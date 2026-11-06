import Mathlib

theorem algebra_306113 :
    IsLeast {x | ∃ a b c : ℝ, x = a * b + b * c + a * c ∧ a ^ 2 + b ^ 2 = 1 ∧ b ^ 2 + c ^ 2 = 2 ∧ a ^ 2 + c ^ 2 = 2} (1 / 2 - Real.sqrt 3) := by
  constructor
  · -- Show that 1 / 2 - Real.sqrt 3 is in the set.
    use (Real.sqrt 2 / 2), (Real.sqrt 2 / 2), (-Real.sqrt 6 / 2)
    constructor
    · -- Show that 1 / 2 - Real.sqrt 3 = a * b + b * c + a * c
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h2 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
      have h3 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
        calc
          Real.sqrt 6 = Real.sqrt (2 * 3) := by norm_num
          _ = Real.sqrt (2) * Real.sqrt (3) := by rw [Real.sqrt_mul (by norm_num)]
          _ = Real.sqrt 2 * Real.sqrt 3 := by ring
      nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, Real.sqrt_nonneg 3, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3) ]
    constructor
    · -- Show that a ^ 2 + b ^ 2 = 1
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [ Real.sqrt_nonneg 2 ]
    constructor
    · -- Show that b ^ 2 + c ^ 2 = 2
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h2 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
      nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg 6 ]
    · -- Show that a ^ 2 + c ^ 2 = 2
      have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h2 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
      nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg 6 ]
  · -- Show that 1 / 2 - Real.sqrt 3 is the minimum.
    intro x hx
    rcases hx with ⟨a, b, c, h_eq, h1, h2, h3⟩
    nlinarith [ sq_nonneg (a - b), sq_nonneg (b + c), sq_nonneg (a - c), 
          sq_nonneg (a + b + c), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)
        ]