import Mathlib

theorem algebra_21535 :
    IsLeast {x : ℝ | ∃ a b c, x = a * b + a * c + b * c ∧ a ^ 2 + b ^ 2 + c ^ 2 = 1} (-1 / 2) := by
  constructor
  · -- Show that -1/2 is in the set
    use Real.sqrt (1 / 6), Real.sqrt (1 / 6), -2 * Real.sqrt (1 / 6)
    constructor
    · -- Show that the value equals -1/2
      nlinarith [Real.sqrt_nonneg (1 / 6), Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 6 by norm_num)]
    · -- Show that the constraint is satisfied
      nlinarith [Real.sqrt_nonneg (1 / 6), Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 6 by norm_num)]
  · -- Show that -1/2 is minimal
    intro x hx
    rcases hx with ⟨a, b, c, hx1, hx2⟩
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]