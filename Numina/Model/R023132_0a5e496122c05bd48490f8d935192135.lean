import Mathlib

/- If the real numbers $a$, $b$, $c$ satisfy ${{a}^{2}}+{{b}^{2}}+{{c}^{2}}=9$, the maximum value of the algebraic expression ${{(a-b)}^{2}}+{{(b-c)}^{2}}+{{(c-a)}^{2}}$ is ___          ___. -/
theorem algebra_7228 : IsGreatest {x : ℝ | ∃ a b c, x = (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 9} 27 := by
  constructor
  · -- Show 27 is in the set
    use 3 * Real.sqrt 2 / 2, -3 * Real.sqrt 2 / 2, 0
    constructor
    · -- Verify the expression equals 27
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Show the constraint is satisfied.
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Show no greater value is in the set
    intro x hx
    rcases hx with ⟨a, b, c, h1, h2⟩
    have h3 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 2 * (a^2 + b^2 + c^2 - (a * b + b * c + c * a)) := by
      ring
    have h4 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 2 * (9 - (a * b + b * c + c * a)) := by
      rw [h3]
      rw [show a^2 + b^2 + c^2 = 9 by linarith [h2]]
    have h5 : a * b + b * c + c * a ≥ -9 / 2 := by
      nlinarith [sq_nonneg (a + b + c), h2]
    nlinarith [h1, h4, h5]