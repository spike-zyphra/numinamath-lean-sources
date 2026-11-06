import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_94382 {f : ℝ → ℝ}
  (hf : ∀ x, f x = abs (x - 2) + abs (x - 4) - abs (2 * x - 6)) :
  IsGreatest (image f (Icc 2 8)) 2 ∧ IsLeast (image f (Icc 2 8)) 0 := by
  constructor
  · -- Show that 2 is greatest in image
    constructor
    · -- Show 2 belongs to image
      use 3
      constructor
      · norm_num
      · norm_num [hf]
        all_goals norm_num [abs_of_pos, abs_of_nonneg, abs_of_nonpos, abs_of_neg]
    · -- Show no greater value belongs
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hx1 : 2 ≤ x := by linarith [hx.1]
      have hx2 : x ≤ 8 := by linarith [hx.2]
      have h1 : f x = abs (x - 2) + abs (x - 4) - abs (2 * x - 6) := hf x
      rw [h1]
      by_cases h1 : x ≥ 4
      · -- x >= 4
        rw [abs_of_nonneg (show x - 2 ≥ 0 by linarith), abs_of_nonneg (show x - 4 ≥ 0 by linarith), abs_of_nonneg (show 2 * x - 6 ≥ 0 by linarith)]
        all_goals nlinarith
      by_cases h2 : x ≥ 3
      · -- 3 <= x < 4
        rw [abs_of_nonneg (show x - 2 ≥ 0 by linarith), abs_of_nonpos (show x - 4 ≤ 0 by linarith), abs_of_nonneg (show 2 * x - 6 ≥ 0 by linarith)]
        all_goals nlinarith
      by_cases h3 : x ≥ 2
      · -- 2 <= x < 3
        rw [abs_of_nonneg (show x - 2 ≥ 0 by linarith), abs_of_nonpos (show x - 4 ≤ 0 by linarith), abs_of_nonpos (show 2 * x - 6 ≤ 0 by linarith)]
        all_goals nlinarith
      all_goals try { nlinarith }
  · -- Show that 0 is least in image
    constructor
    · -- Show 0 belongs to image
      use 2
      constructor
      · norm_num
      · norm_num [hf]
        all_goals norm_num [abs_of_pos, abs_of_nonneg, abs_of_nonpos, abs_of_neg]
    · -- Show no less value belongs
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hx1 : 2 ≤ x := by linarith [hx.1]
      have hx2 : x ≤ 8 := by linarith [hx.2]
      have h1 : f x = abs (x - 2) + abs (x - 4) - abs (2 * x - 6) := hf x
      rw [h1]
      by_cases h1 : x ≥ 4
      · -- x >= 4
        rw [abs_of_nonneg (show x - 2 ≥ 0 by linarith), abs_of_nonneg (show x - 4 ≥ 0 by linarith), abs_of_nonneg (show 2 * x - 6 ≥ 0 by linarith)]
        all_goals nlinarith
      by_cases h2 : x ≥ 3
      · -- 3 <= x < 4
        rw [abs_of_nonneg (show x - 2 ≥ 0 by linarith), abs_of_nonpos (show x - 4 ≤ 0 by linarith), abs_of_nonneg (show 2 * x - 6 ≥ 0 by linarith)]
        all_goals nlinarith
      by_cases h3 : x ≥ 2
      · -- 2 <= x < 3
        rw [abs_of_nonneg (show x - 2 ≥ 0 by linarith), abs_of_nonpos (show x - 4 ≤ 0 by linarith), abs_of_nonpos (show 2 * x - 6 ≤ 0 by linarith)]
        all_goals nlinarith
      all_goals try { nlinarith }