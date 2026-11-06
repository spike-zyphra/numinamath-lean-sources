import Mathlib

theorem algebra_225601 (f g : ℝ → ℝ) (hf : f = fun x => abs (x^2 - x - 2)) (hg : g = fun x => 2 * x) :
    f 1 = g 1 ∧ f ((3 + Real.sqrt 17) / 2) = g ((3 + Real.sqrt 17) / 2) := by
  have h1 : f 1 = g 1 := by
    rw [hf, hg]
    norm_num [abs_of_nonneg, abs_of_nonpos]
    all_goals norm_num
  have h2 : f ((3 + Real.sqrt 17) / 2) = g ((3 + Real.sqrt 17) / 2) := by
    rw [hf, hg]
    have h3 : ((3 + Real.sqrt 17) / 2 : ℝ) ^ 2 - ((3 + Real.sqrt 17) / 2 : ℝ) - 2 = 3 + Real.sqrt 17 := by
      nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), sq_nonneg (Real.sqrt 17 ^ 2 - 17)]
    have h4 : abs (((3 + Real.sqrt 17) / 2 : ℝ) ^ 2 - ((3 + Real.sqrt 17) / 2 : ℝ) - 2) = 3 + Real.sqrt 17 := by
      rw [h3]
      all_goals
        apply abs_of_nonneg
        positivity
    simp only [h4]
    <;> ring_nf <;> norm_num
    <;> nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
  constructor
  · exact h1
  · exact h2