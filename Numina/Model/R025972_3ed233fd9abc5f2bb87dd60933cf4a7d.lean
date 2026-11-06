import Mathlib

theorem algebra_156232 (x y : ℝ) (h : x^2 + y^2 - 3 * y - 1 = 0) :
    x + y ≤ (Real.sqrt 26 + 3) / 2 ∧ ∃ x y, x^2 + y^2 - 3 * y - 1 = 0 ∧ x + y = (Real.sqrt 26 + 3) / 2 := by
  constructor
  · -- First part: to prove $x + y \leq \frac{\sqrt{26} + 3}{2}$
    nlinarith [sq_nonneg (x - Real.sqrt 26 / 4), sq_nonneg (y - (Real.sqrt 26 / 4 + 3 / 2)), Real.sqrt_nonneg 26, Real.sq_sqrt (show 0 ≤ (26 : ℝ) by norm_num), Real.sqrt_pos.mpr (by norm_num : (26 : ℝ) > 0)]
  · -- Second part: to prove existence of $x, y$ satisfying the equality
    use Real.sqrt 26 / 4, Real.sqrt 26 / 4 + 3 / 2
    constructor
    · -- Show constraint is satisfied
      nlinarith [Real.sq_sqrt (show 0 ≤ (26 : ℝ) by norm_num), Real.sqrt_nonneg 26]
    · -- Show $x + y = \frac{\sqrt{26} + 3}{2}$
      ring_nf
      <;> field_simp
      <;> ring