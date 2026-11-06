import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_295010 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = abs (x - 2) + abs (x - 4) - abs (2 * x - 6)) :
  IsGreatest (image f (Icc 2 8)) 2 ∧ IsLeast (image f (Icc 2 8)) 0 := by
  constructor
  · -- Show 2 is greatest element
    constructor
    · -- Show 2 is in image
      use 3
      constructor
      · -- Show 3 in [2,8]
        norm_num [mem_Icc]
      · -- Compute f 3
        rw [h₀]
        norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Show upper bound
      intro y hy
      rcases hy with ⟨x, hx, hfx⟩
      have hx1 : 2 ≤ x := by
        have h1 : x ∈ Icc (2 : ℝ) 8 := by simpa using hx
        exact h1.1
      have hx2 : x ≤ 8 := by
        have h1 : x ∈ Icc (2 : ℝ) 8 := by simpa using hx
        exact h1.2
      by_cases h1 : x ≤ 3
      · -- Case 1: 2 ≤ x ≤ 3
        have hfx1 : f x = 2 * x - 4 := by
          rw [h₀ x]
          rw [abs_of_nonneg (show (x - 2 : ℝ) ≥ 0 by linarith),
              abs_of_nonpos (show (x - 4 : ℝ) ≤ 0 by linarith),
              abs_of_nonpos (show (2 * x - 6 : ℝ) ≤ 0 by linarith)]
          all_goals linarith 
        rw [hfx1] at hfx
        have : 2 * x - 4 ≤ 2 := by linarith
        linarith
      · -- Case 2: 3 < x ≤ 8
        by_cases h2 : x ≤ 4
        · -- Subcase 2.1: 3 < x ≤ 4
          have hfx1 : f x = -2 * x + 8 := by
            rw [h₀ x]
            rw [abs_of_nonneg (show (x - 2 : ℝ) ≥ 0 by linarith),
                abs_of_nonpos (show (x - 4 : ℝ) ≤ 0 by linarith),
                abs_of_pos (show (2 * x - 6 : ℝ) > 0 by linarith)]
            all_goals linarith
          rw [hfx1] at hfx
          have : -2 * x + 8 ≤ 2 := by linarith
          linarith
        · -- Subcase 2.2: 4 < x ≤ 8
          have hfx1 : f x = (0 : ℝ) := by
            rw [h₀ x]
            rw [abs_of_nonneg (show (x - 2 : ℝ) ≥ 0 by linarith),
                abs_of_nonneg (show (x - 4 : ℝ) ≥ 0 by linarith),
                abs_of_pos (show (2 * x - 6 : ℝ) > 0 by linarith)]
            all_goals linarith 
          rw [hfx1] at hfx
          norm_num at hfx ⊢
          all_goals linarith
  · -- Show 0 is least element
    constructor
    · -- Show 0 is in image
      use 2
      constructor
      · -- Show 2 in [2,8]
        norm_num [mem_Icc]
      · -- Compute f 2
        rw [h₀]
        norm_num [abs_of_nonneg, abs_of_nonpos]
        all_goals linarith 
    · -- Show lower bound
      intro y hy
      rcases hy with ⟨x, hx, hfx⟩
      have hx1 : 2 ≤ x := by
        have h1 : x ∈ Icc (2 : ℝ) 8 := by simpa using hx
        exact h1.1
      have hx2 : x ≤ 8 := by
        have h1 : x ∈ Icc (2 : ℝ) 8 := by simpa using hx
        exact h1.2
      by_cases h1 : x ≤ 3
      · -- Case 1: 2 ≤ x ≤ 3
        have hfx1 : f x = 2 * x - 4 := by
          rw [h₀ x]
          rw [abs_of_nonneg (show (x - 2 : ℝ) ≥ 0 by linarith),
              abs_of_nonpos (show (x - 4 : ℝ) ≤ 0 by linarith),
              abs_of_nonpos (show (2 * x - 6 : ℝ) ≤ 0 by linarith)]
          all_goals linarith 
        rw [hfx1] at hfx
        have : 0 ≤ 2 * x - 4 := by linarith
        linarith
      · -- Case 2: 3 < x ≤ 8
        by_cases h2 : x ≤ 4
        · -- Subcase 2.1: 3 < x ≤ 4
          have hfx1 : f x = -2 * x + 8 := by
            rw [h₀ x]
            rw [abs_of_nonneg (show (x - 2 : ℝ) ≥ 0 by linarith),
                abs_of_nonpos (show (x - 4 : ℝ) ≤ 0 by linarith),
                abs_of_pos (show (2 * x - 6 : ℝ) > 0 by linarith)]
            all_goals linarith
          rw [hfx1] at hfx
          have : 0 ≤ -2 * x + 8 := by linarith
          linarith
        · -- Subcase 2.2: 4 < x ≤ 8
          have hfx1 : f x = (0 : ℝ) := by
            rw [h₀ x]
            rw [abs_of_nonneg (show (x - 2 : ℝ) ≥ 0 by linarith),
                abs_of_nonneg (show (x - 4 : ℝ) ≥ 0 by linarith),
                abs_of_pos (show (2 * x - 6 : ℝ) > 0 by linarith)]
            all_goals linarith 
          rw [hfx1] at hfx
          norm_num at hfx ⊢
          all_goals linarith