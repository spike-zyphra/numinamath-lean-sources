import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_103056 {f : ℝ → ℝ} (hf : f = λ x => (1/2)^abs (x-2)) :
    ∀ x, f x = 1 ↔ x = 2 := by
  intro x
  constructor
  · -- Assume f x = 1, show x = 2
    intro hfx
    rw [hf] at hfx
    have h1 : (1 / 2 : ℝ) ^ abs (x - 2) = 1 := hfx
    have h2 : abs (x - 2) = (0 : ℝ) := by
      apply_fun (Real.logb (1 / 2 : ℝ)) at h1
      have h3 : Real.logb (1 / 2 : ℝ) ((1 / 2 : ℝ) ^ abs (x - 2)) = Real.logb (1 / 2 : ℝ) (1 : ℝ) := by
        rw [h1]
      have h4 : Real.logb (1 / 2 : ℝ) ((1 / 2 : ℝ) ^ abs (x - 2)) = abs (x - 2) := by
        rw [Real.logb_rpow]
        all_goals norm_num
      have h5 : Real.logb (1 / 2 : ℝ) (1 : ℝ) = (0 : ℝ) := by
        simp [Real.logb_one]
      rw [h4, h5] at h3
      linarith
    have h3 : x - 2 = 0 := by
      simpa [abs_eq_zero] using h2
    linarith
  · -- Assume x = 2, show f x = 1
    intro hfx
    rw [hf]
    rw [hfx]
    norm_num
    all_goals norm_num