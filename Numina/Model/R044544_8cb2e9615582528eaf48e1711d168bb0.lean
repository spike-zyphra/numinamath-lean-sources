import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_207391 :
  IsLeast {t : ℝ | ∃ x y z : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧
    x^2 + y^2 + z^2 + x + 2 * y + 3 * z = 13 / 4 ∧ t = x + y + z} ((-3 + sqrt 22) / 2) := by
  constructor
  · -- Show that $(-3 + \sqrt{22}) / 2$ is in the set.
    use 0, 0, (-3 + sqrt 22) / 2
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · -- Show $z \geq 0$.
      have h1 : sqrt 22 ≥ 0 := by positivity
      have h2 : (-3 + sqrt 22) / 2 ≥ 0 := by
        nlinarith [Real.sqrt_nonneg (22 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (22 : ℝ) by norm_num)]
      linarith
    constructor
    · -- Show $x^2 + y^2 + z^2 + x + 2 * y + 3 * z = 13 / 4$.
      nlinarith [Real.sqrt_nonneg (22 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (22 : ℝ) by norm_num)]
    · -- Show $t = x + y + z$.
      norm_num
  · -- Show that $(-3 + \sqrt{22}) / 2$ is the minimum.
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h1, h2⟩
    nlinarith [sq_nonneg (x - 0), sq_nonneg (y - 0), sq_nonneg (z - (-3 + Real.sqrt 22) / 2), 
      Real.sqrt_nonneg (22: ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (22 : ℝ) by norm_num), 
      sq_nonneg (x + 1 / 2), sq_nonneg (y + 1), sq_nonneg (z + 3 / 2)]