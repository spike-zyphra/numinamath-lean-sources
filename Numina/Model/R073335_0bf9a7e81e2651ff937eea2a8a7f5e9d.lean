import Mathlib

theorem algebra_2796 (x : ℝ) :
  abs (x + 3) + abs (3 - x) = 9 / 2 * abs x + 5 ↔
  x = 2 / 9 ∨ x = -2 / 9 := by
  constructor
  · -- Forward implication: equation implies solutions
    intro h
    by_cases h1 : x ≥ 0
    · -- x ≥ 0, so abs x = x
      rw [abs_of_nonneg (show x ≥ 0 by linarith)] at h
      by_cases h2 : x + 3 ≥ 0
      · -- x + 3 ≥ 0, so abs (x + 3) = x + 3
        rw [abs_of_nonneg h2] at h
        by_cases h3 : 3 - x ≥ 0
        · -- 3 - x ≥ 0, so abs (3 - x) = 3 - x
          rw [abs_of_nonneg h3] at h
          have hx : x = 2 / 9 := by linarith
          left
          exact hx
        · -- 3 - x < 0, so abs (3 - x) = x - 3
          rw [abs_of_neg (show 3 - x < 0 by linarith)] at h
          exfalso
          linarith
      · -- x + 3 < 0, impossible because x ≥ 0
        rw [abs_of_neg (show x + 3 < 0 by linarith)] at h
        exfalso
        linarith
    · -- x < 0, so abs x = -x
      rw [abs_of_neg (show x < 0 by linarith)] at h
      by_cases h3 : x + 3 ≥ 0
      · -- x + 3 ≥ 0, so abs (x + 3) = x + 3
        rw [abs_of_nonneg h3] at h
        by_cases h4 : 3 - x ≥ 0
        · -- 3 - x ≥ 0, so abs (3 - x) = 3 - x
          rw [abs_of_nonneg h4] at h
          have hx : x = -2 / 9 := by linarith
          right
          exact hx
        · -- 3 - x < 0, impossible because x < 0
          rw [abs_of_neg (show 3 - x < 0 by linarith)] at h
          exfalso
          linarith
      · -- x + 3 < 0, so abs (x + 3) = -(x + 3)
        rw [abs_of_neg (show x + 3 < 0 by linarith)] at h
        by_cases h4 : 3 - x ≥ 0
        · -- 3 - x ≥ 0, so abs (3 - x) = 3 - x
          rw [abs_of_nonneg h4] at h
          exfalso
          linarith
        · -- 3 - x < 0, impossible because x < 0
          rw [abs_of_neg (show 3 - x < 0 by linarith)] at h
          exfalso
          linarith
  · -- Backward direction: solutions satisfy equation
    rintro (hx | hx)
    · -- x = 2/9
      rw [hx]
      norm_num [abs_of_nonneg]
      all_goals
        norm_num [abs_of_nonneg]
    · -- x = -2/9
      rw [hx]
      norm_num [abs_of_nonneg, abs_of_neg]
      all_goals
        norm_num [abs_of_nonneg, abs_of_neg]