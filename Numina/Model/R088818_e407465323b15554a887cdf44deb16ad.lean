import Mathlib

open Real

theorem algebra_8464 {f : ℝ → ℝ} (hf : f = fun x => x - 1 / (2 * x)) :
    (∀ x, f (-x) = -f x) ∧ (∃ x1 x2, x1 ≠ x2 ∧ f x1 = 0 ∧ f x2 = 0) := by

  constructor
  · -- Show that the function is an odd function.
    intro x
    rw [hf]
    simp
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num
  · -- Show that there are two distinct roots.
    use Real.sqrt 0.5, -Real.sqrt 0.5
    constructor
    · -- Show that sqrt(0.5) ≠ -sqrt(0.5).
      have h1 : Real.sqrt 0.5 > 0 := by
        apply Real.sqrt_pos.mpr
        norm_num
        all_goals norm_num
      have h2 : -Real.sqrt 0.5 < 0 := by
        linarith [Real.sqrt_nonneg 0.5]
      intro h
      linarith [h1, h2, show Real.sqrt 0.5 = -Real.sqrt 0.5 from by linarith]
    constructor
    · -- Show that f (Real.sqrt 0.5) = 0
      rw [hf]
      simp
      have h1 : (Real.sqrt 0.5 : ℝ) ^ 2 = (0.5 : ℝ) := Real.sq_sqrt (by norm_num)
      have h2 : (Real.sqrt 0.5 : ℝ) ≠ 0 := by positivity
      field_simp [h1]
      <;> nlinarith [Real.sqrt_nonneg (0.5 : ℝ), Real.sq_sqrt (show (0.5 : ℝ) ≥ 0 by norm_num)]
    · -- Show that f (-Real.sqrt 0.5) = 0
      rw [hf]
      simp
      have h1 : (Real.sqrt 0.5 : ℝ) ^ 2 = (0.5 : ℝ) := Real.sq_sqrt (by norm_num)
      have h2 : (Real.sqrt 0.5 : ℝ) ≠ 0 := by positivity
      field_simp [h1]
      <;> nlinarith [Real.sqrt_nonneg (0.5 : ℝ), Real.sq_sqrt (show (0.5 : ℝ) ≥ 0 by norm_num)]