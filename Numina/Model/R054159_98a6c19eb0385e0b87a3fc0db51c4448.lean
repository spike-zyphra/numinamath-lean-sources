import Mathlib

theorem algebra_236460 {f : ℝ → ℝ} (hf : f = fun x => x^2 + 2 * x - 5) :
    f (f (-1 / 2 * (1 + Real.sqrt 21))) = -1 / 2 * (1 + Real.sqrt 21) ∧
    f (f (-1 / 2 * (3 + Real.sqrt 17))) = -1 / 2 * (3 + Real.sqrt 17) := by
  constructor
  · -- Let's verify $f(f(-1/2*(1 + √21))) = -1/2*(1 + √21)$
    rw [hf]
    -- Compute f(-1/2*(1 + √21))
    -- Let $x = -1/2*(1 + √21)$
    -- Compute x^2 + 2x - 5 = -1/2*(1 + √21)
    have h2 : ((-1 / 2 * (1 + Real.sqrt 21)) : ℝ) ^ 2 + 2 * (-1 / 2 * (1 + Real.sqrt 21)) - 5 = -1 / 2 * (1 + Real.sqrt 21) := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (21 : ℝ) by norm_num), 
          Real.sqrt_nonneg 21, 
          Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]
    simp [h2]
    <;> ring_nf <;> norm_num
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (21 : ℝ) by norm_num), 
        Real.sqrt_nonneg 21, 
        Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]
  · -- Let's verify $f(f(-1/2*(3 + √17))) = -1/2*(3 + √17)$
    rw [hf]
    -- Compute f(f(-1/2*(3 + √17)))
    have eq1 : ((-1 / 2 * (3 + Real.sqrt 17)) : ℝ) ^ 2 + 2 * (-1 / 2 * (3 + Real.sqrt 17)) - 5 = (-3 / 2 + Real.sqrt 17 / 2 : ℝ) := by 
      nlinarith [Real.sqrt_pos.mpr (show 0 < (17 : ℝ) by norm_num), 
          Real.sqrt_nonneg 17, 
          Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
    have eq2 : ((-3 / 2 + Real.sqrt 17 / 2 : ℝ) : ℝ) ^ 2 + 2 * (-3 / 2 + Real.sqrt 17 / 2 : ℝ) - 5 = (-1 / 2 * (3 + Real.sqrt 17) : ℝ) := by 
      nlinarith [Real.sqrt_pos.mpr (show 0 < (17 : ℝ) by norm_num), 
          Real.sqrt_nonneg 17, 
          Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
    simp [eq1, eq2]
    <;> ring_nf <;> norm_num
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (17 : ℝ) by norm_num), 
        Real.sqrt_nonneg 17, 
        Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]