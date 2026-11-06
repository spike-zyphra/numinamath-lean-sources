import Mathlib

/- Let $2x + y - \sqrt{5}z = 2$, then the minimum value of $x^{2} + y^{2} + z^{2}$ is ___          ___. -/
theorem algebra_8298 :
  IsLeast {t : ℝ | ∃ x y z, t = x^2 + y^2 + z^2 ∧ 2 * x + y - Real.sqrt 5 * z = 2} (2 / 5) := by
  constructor
  · -- Show that 2/5 is in the set
    use 2 / 5, 1 / 5, -Real.sqrt 5 / 5
    constructor
    · -- Verify that x^2 + y^2 + z^2 = 2/5
      have h1 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)]
    · -- Verify that 2x + y - sqrt 5 * z = 2
      have h1 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)]
  · -- Show that no number less than 2/5 is in the set
    intro t ht
    rcases ht with ⟨x, y, z, ht1, ht2⟩
    have h1 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h4 : (2 * x + y - Real.sqrt 5 * z) ^ 2 ≤ (2 ^ 2 + 1 ^ 2 + (Real.sqrt 5) ^ 2) * (x^2 + y^2 + z^2) := by
      have h1 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      nlinarith [sq_nonneg (2 * x - y), sq_nonneg (y + Real.sqrt 5 * z), sq_nonneg (2 * x + Real.sqrt 5 * z), sq_nonneg (x - 2 / 5), sq_nonneg (y - 1 / 5), sq_nonneg (z + Real.sqrt 5 / 5), Real.sqrt_nonneg 5, sq_nonneg (y + Real.sqrt 5 * (x)), sq_nonneg (2 * x - y + Real.sqrt 5 * z), Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
    have h3 : (2 * x + y - Real.sqrt 5 * z) ^ 2 = 4 := by
      rw [ht2]
      norm_num
    nlinarith [ht1, h3, Real.sqrt_nonneg 5, h1, sq_nonneg (x - 2 / 5), sq_nonneg (y - 1 / 5), sq_nonneg (z + Real.sqrt 5 / 5)]