import Mathlib

theorem algebra_144782 (f : ℝ → ℝ) (hf : ∀ x, f x ∈ Set.Icc (3 / 8) (4 / 9)) :
    ∀ x, f x + Real.sqrt (1 - 2 * f x) ∈ Set.Icc (7 / 9) (7 / 8) := by
  intro x
  have hfx : f x ∈ Set.Icc (3 / 8) (4 / 9) := hf x
  rcases hfx with ⟨h1, h2⟩
  have h3 : 0 ≤ 1 - 2 * f x := by
    nlinarith
  have h4 : Real.sqrt (1 - 2 * f x) ≥ 0 := by
    apply Real.sqrt_nonneg
  have hfx1 : f x + Real.sqrt (1 - 2 * f x) ≤ 7 / 8 := by
    nlinarith [Real.sqrt_nonneg (1 - 2 * f x), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - 2 * f x by linarith), sq_nonneg (f x - 3 / 8), sq_nonneg (f x - 4 / 9), sq_nonneg (Real.sqrt (1 - 2 * f x) - 1)]
  have hfx2 : f x + Real.sqrt (1 - 2 * f x) ≥ 7 / 9 := by
    nlinarith [Real.sqrt_nonneg (1 - 2 * f x), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - 2 * f x by linarith), sq_nonneg (f x - 3 / 8), sq_nonneg (f x - 4 / 9), sq_nonneg (Real.sqrt (1 - 2 * f x) - 1 / 3)]
  constructor
  · -- Prove the lower bound
    linarith [hfx2]
  · -- Prove the upper bound
    linarith [hfx1]