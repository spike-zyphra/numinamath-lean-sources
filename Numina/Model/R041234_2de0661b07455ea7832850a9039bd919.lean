import Mathlib

theorem algebra_152890 (f g : ℝ → ℝ)
    (hf : f = fun x => x^2 * (x - 3)^2)
    (hg : g = fun x => (x^2 - 1) * (x - 2)) :
    ∃ x1 x2 x3 x4 : ℝ,
      f x1 = g x1 ∧ f x2 = g x2 ∧ f x3 = g x3 ∧ f x4 = g x4 ∧
      x1 + x2 + x3 + x4 = 7 := by
  use 1 + Real.sqrt 2, 1 - Real.sqrt 2, (5 + Real.sqrt 17) / 2, (5 - Real.sqrt 17) / 2
  constructor
  · -- Show that f(1 + Real.sqrt 2) = g(1 + Real.sqrt 2)
    rw [hf, hg]
    simp
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
  constructor
  · -- Show that f(1 - Real.sqrt 2) = g(1 - Real.sqrt 2)
    rw [hf, hg]
    simp
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) ]
  constructor
  · -- Show that f((5 + Real.sqrt 17) / 2) = g((5 + Real.sqrt 17) / 2)
    rw [hf, hg]
    simp
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < (17 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num) ]
  constructor
  · -- Show that f((5 - Real.sqrt 17) / 2) = g((5 - Real.sqrt 17) / 2)
    rw [hf, hg]
    simp
    nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < (17 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num) ]
  · -- Show that the sum of the x-coordinates is 7
    ring