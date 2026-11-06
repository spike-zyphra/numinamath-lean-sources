import Mathlib

open Real

theorem inequalities_314718 (a : ℝ) :
    (∀ x : ℝ, abs (x + a) - abs (x + 1) ≤ 2 * a) ↔
    a ≥ 1 / 3 := by 
  constructor
  · -- Assume the inequality holds for all $x$, prove $a \geq 1/3$.
    intro h
    have h1 := h (-1)
    have h2 : abs (-1 + a) = abs (a - 1) := by
      ring_nf
    have h3 : abs (-1 + (1 : ℝ)) = (0 : ℝ) := by
      norm_num
    have h4 : abs (a - 1) ≤ 2 * a := by 
      have eq : abs (-1 + a) - abs (-1 + (1 : ℝ)) = abs (a - 1) := by
        rw [h2, h3]
        all_goals norm_num
      linarith [eq, h1]
    by_cases h6 : a ≥ 0 
    · -- Assume a ≥0.
      by_cases h5c : a -1 < 0
      · -- Assume a -1 < 0 : a <1.
        rw [abs_of_neg (show a -1 <0 by linarith)] at h4
        nlinarith
      · -- Assume a -1 ≥0 : a ≥1.
        rw [abs_of_nonneg (show a -1 ≥0 by linarith)] at h4
        nlinarith
    · -- Assume a < 0.
      have h6a : abs (a -1) ≥0 := by
        apply abs_nonneg
      have h6b : 2 * a ≥ 0 := by 
        linarith [h4, h6a]
      nlinarith
  · -- Assume $a \geq 1/3$, prove the inequality holds for all $x$.
    intro h x
    by_cases h1 : x + a ≥ 0
    · -- Assume |x+a|=x+a.
      rw [abs_of_nonneg h1]
      by_cases h2 : x + 1 ≥ 0 
      · -- Assume |x+1|=x+1.
        rw [abs_of_nonneg h2]
        nlinarith
      · -- Assume |x+1|=-x-1.
        rw [abs_of_neg (show x + 1 < 0 by linarith)]
        nlinarith
    · -- Assume |x+a|=-x-a.
      rw [abs_of_neg (show x + a < 0 by linarith)]
      by_cases h2 : x + 1 ≥ 0 
      · -- Assume |x+1|=x+1.
        rw [abs_of_nonneg h2]
        nlinarith
      · -- Assume |x+1|=-x-1.
        rw [abs_of_neg (show x + 1 < 0 by linarith)]
        nlinarith