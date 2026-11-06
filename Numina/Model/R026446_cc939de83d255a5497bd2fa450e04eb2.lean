import Mathlib

theorem algebra_115075 (f : ℝ → ℝ) (hf : f = fun x => abs (2 * x - 5) + abs (3 * x - 7) + abs (5 * x - 11)) :
    {x | f x = 2015 / 2016}.encard = 0 := by
  have h1 : ∀ x : ℝ, f x ≥ 1 := by
    intro x
    rw [hf]
    simp
    by_cases h1 : 2 * x - 5 ≥ 0
    · -- case 2x - 5 ≥ 0
      rw [abs_of_nonneg h1]
      by_cases h2 : 3 * x - 7 ≥ 0
      · -- case 3x - 7 ≥ 0
        rw [abs_of_nonneg h2]
        by_cases h3 : 5 * x - 11 ≥ 0
        · -- case 5x - 11 ≥ 0
          rw [abs_of_nonneg h3]
          linarith
        · -- case 5x - 11 < 0
          rw [abs_of_neg (show 5 * x - 11 < 0 by linarith)]
          linarith
      · -- case 3x - 7 < 0
        rw [abs_of_neg (show 3 * x - 7 < 0 by linarith)]
        by_cases h3 : 5 * x - 11 ≥ 0
        · -- case 5x - 11 ≥ 0
          rw [abs_of_nonneg h3]
          linarith
        · -- case 5x - 11 < 0
          rw [abs_of_neg (show 5 * x - 11 < 0 by linarith)]
          linarith
    · -- case 2x - 5 < 0
      rw [abs_of_neg (show 2 * x - 5 < 0 by linarith)]
      by_cases h2 : 3 * x - 7 ≥ 0
      · -- case 3x - 7 ≥ 0
        rw [abs_of_nonneg h2]
        by_cases h3 : 5 * x - 11 ≥ 0
        · -- case 5x - 11 ≥ 0
          rw [abs_of_nonneg h3]
          linarith
        · -- case 5x - 11 < 0
          rw [abs_of_neg (show 5 * x - 11 < 0 by linarith)]
          linarith
      · -- case 3x - 7 < 0
        rw [abs_of_neg (show 3 * x - 7 < 0 by linarith)]
        by_cases h3 : 5 * x - 11 ≥ 0
        · -- case 5x - 11 ≥ 0
          rw [abs_of_nonneg h3]
          linarith
        · -- case 5x - 11 < 0
          rw [abs_of_neg (show 5 * x - 11 < 0 by linarith)]
          linarith
  have h2 : ∀ x : ℝ, f x ≠ 2015 / 2016 := by
    intro x
    intro heq
    have h3 : f x ≥ 1 := h1 x
    linarith
  have h3 : {x : ℝ | f x = 2015 / 2016} = ∅ := by
    ext x
    simp [h2]
  rw [h3]
  simp