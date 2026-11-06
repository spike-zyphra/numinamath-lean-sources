import Mathlib

open Real Set

theorem algebra_318745 (f : ℝ → ℝ) (hf : f = fun x => abs (x + 1) + abs (x + 2) + abs (x + 3) + abs (x + 4) + abs (x + 5)) :
    IsLeast (range f) 6 := by
  unfold IsLeast
  constructor
  · -- Let's prove 6 is in the range first
    use -3
    norm_num [hf]
  · -- Now to prove 6 is a lower bound
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    by_cases h1 : x + 1 ≥ 0
    · -- Case 1: x + 1 ≥ 0
      rw [abs_of_nonneg (by linarith)] at hx
      by_cases h2 : x + 2 ≥ 0
      · -- Case 1a: x + 2 ≥ 0
        rw [abs_of_nonneg (by linarith)] at hx
        by_cases h3 : x + 3 ≥ 0
        · -- Case 1a1: x + 3 ≥ 0
          rw [abs_of_nonneg (by linarith)] at hx
          by_cases h4 : x + 4 ≥ 0
          · -- Case 1a1a: x + 4 ≥ 0
            rw [abs_of_nonneg (by linarith)] at hx
            by_cases h5 : x + 5 ≥ 0
            · -- Case 1a1a1: x + 5 ≥ 0
              rw [abs_of_nonneg (by linarith)] at hx
              linarith
            · -- Case 1a1a2: x + 5 < 0
              rw [abs_of_neg (by linarith)] at hx
              linarith
          · -- Case 1a1b: x + 4 < 0
            rw [abs_of_neg (by linarith)] at hx
            by_cases h5 : x + 5 ≥ 0
            · -- Case 1a1b1: x + 5 ≥ 0
              rw [abs_of_nonneg (by linarith)] at hx
              linarith
            · -- Case 1a1b2: x + 5 < 0
              rw [abs_of_neg (by linarith)] at hx
              linarith
        · -- Case 1a2: x + 3 < 0
          rw [abs_of_neg (by linarith)] at hx
          by_cases h4 : x + 4 ≥ 0
          · -- Case 1a2a: x + 4 ≥ 0
            rw [abs_of_nonneg (by linarith)] at hx
            by_cases h5 : x + 5 ≥ 0
            · -- Case 1a2a1: x + 5 ≥ 0
              rw [abs_of_nonneg (by linarith)] at hx
              linarith
            · -- Case 1a2a2: x + 5 < 0
              rw [abs_of_neg (by linarith)] at hx
              linarith
          · -- Case 1a2b: x + 4 < 0
            rw [abs_of_neg (by linarith)] at hx
            by_cases h5 : x + 5 ≥ 0
            · -- Case 1a2b1: x + 5 ≥ 0
              rw [abs_of_nonneg (by linarith)] at hx
              linarith
            · -- Case 1a2b2: x + 5 < 0
              rw [abs_of_neg (by linarith)] at hx
              linarith
      · -- Case 1b: x + 2 < 0
        rw [abs_of_neg (by linarith)] at hx
        by_cases h3 : x + 3 ≥ 0
        · -- Case 1b1: x + 3 ≥ 0
          rw [abs_of_nonneg (by linarith)] at hx
          by_cases h4 : x + 4 ≥ 0
          · -- Case 1b1a: x + 4 ≥ 0
            rw [abs_of_nonneg (by linarith)] at hx
            by_cases h5 : x + 5 ≥ 0
            · -- Case 1b1a1: x + 5 ≥ 0
              rw [abs_of_nonneg (by linarith)] at hx
              linarith
            · -- Case 1b1a2: x + 5 < 0
              rw [abs_of_neg (by linarith)] at hx
              linarith
          · -- Case 1b1b: x + 4 < 0
            rw [abs_of_neg (by linarith)] at hx
            by_cases h5 : x + 5 ≥ 0
            · -- Case 1b1b1: x + 5 ≥ 0
              rw [abs_of_nonneg (by linarith)] at hx
              linarith
            · -- Case 1b1b2: x + 5 < 0
              rw [abs_of_neg (by linarith)] at hx
              linarith
        · -- Case 1b2: x + 3 < 0
          rw [abs_of_neg (by linarith)] at hx
          by_cases h4 : x + 4 ≥ 0
          · -- Case 1b2a: x + 4 ≥ 0
            rw [abs_of_nonneg (by linarith)] at hx
            by_cases h5 : x + 5 ≥ 0
            · -- Case 1b2a1: x + 5 ≥ 0
              rw [abs_of_nonneg (by linarith)] at hx
              linarith
            · -- Case 1b2a2: x + 5 < 0
              rw [abs_of_neg (by linarith)] at hx
              linarith
          · -- Case 1b2b: x + 4 < 0
            rw [abs_of_neg (by linarith)] at hx
            by_cases h5 : x + 5 ≥ 0
            · -- Case 1b2b1: x + 5 ≥ 0
              rw [abs_of_nonneg (by linarith)] at hx
              linarith
            · -- Case 1b2b2: x + 5 < 0
              rw [abs_of_neg (by linarith)] at hx
              linarith
    · -- Case 2: x + 1 < 0
      rw [abs_of_neg (by linarith)] at hx
      by_cases h2 : x + 2 ≥ 0
      · -- Case 2a: x + 2 ≥ 0
        rw [abs_of_nonneg (by linarith)] at hx
        by_cases h3 : x + 3 ≥ 0
        · -- Case 2a1: x + 3 ≥ 0
          rw [abs_of_nonneg (by linarith)] at hx
          by_cases h4 : x + 4 ≥ 0
          · -- Case 2a1a: x + 4 ≥ 0
            rw [abs_of_nonneg (by linarith)] at hx
            by_cases h5 : x + 5 ≥ 0
            · -- Case 2a1a1: x + 5 ≥ 0
              rw [abs_of_nonneg (by linarith)] at hx
              linarith
            · -- Case 2a1a2: x + 5 < 0
              rw [abs_of_neg (by linarith)] at hx
              linarith
          · -- Case 2a1b: x + 4 < 0
            rw [abs_of_neg (by linarith)] at hx
            by_cases h5 : x + 5 ≥ 0
            · -- Case 2a1b1: x + 5 ≥ 0
              rw [abs_of_nonneg (by linarith)] at hx
              linarith
            · -- Case 2a1b2: x + 5 < 0
              rw [abs_of_neg (by linarith)] at hx
              linarith
        · -- Case 2a2: x + 3 < 0
          rw [abs_of_neg (by linarith)] at hx
          by_cases h4 : x + 4 ≥ 0
          · -- Case 2a2a: x + 4 ≥ 0
            rw [abs_of_nonneg (by linarith)] at hx
            by_cases h5 : x + 5 ≥ 0
            · -- Case 2a2a1: x + 5 ≥ 0
              rw [abs_of_nonneg (by linarith)] at hx
              linarith
            · -- Case 2a2a2: x + 5 < 0
              rw [abs_of_neg (by linarith)] at hx
              linarith
          · -- Case 2a2b: x + 4 < 0
            rw [abs_of_neg (by linarith)] at hx
            by_cases h5 : x + 5 ≥ 0
            · -- Case 2a2b1: x + 5 ≥ 0
              rw [abs_of_nonneg (by linarith)] at hx
              linarith
            · -- Case 2a2b2: x + 5 < 0
              rw [abs_of_neg (by linarith)] at hx
              linarith
      · -- Case 2b: x + 2 < 0
        rw [abs_of_neg (by linarith)] at hx
        by_cases h3 : x + 3 ≥ 0
        · -- Case 2b1: x + 3 ≥ 0
          rw [abs_of_nonneg (by linarith)] at hx
          by_cases h4 : x + 4 ≥ 0
          · -- Case 2b1a: x + 4 ≥ 0
            rw [abs_of_nonneg (by linarith)] at hx
            by_cases h5 : x + 5 ≥ 0
            · -- Case 2b1a1: x + 5 ≥ 0
              rw [abs_of_nonneg (by linarith)] at hx
              linarith
            · -- Case 2b1a2: x + 5 < 0
              rw [abs_of_neg (by linarith)] at hx
              linarith
          · -- Case 2b1b: x + 4 < 0
            rw [abs_of_neg (by linarith)] at hx
            by_cases h5 : x + 5 ≥ 0
            · -- Case 2b1b1: x + 5 ≥ 0
              rw [abs_of_nonneg (by linarith)] at hx
              linarith
            · -- Case 2b1b2: x + 5 < 0
              rw [abs_of_neg (by linarith)] at hx
              linarith
        · -- Case 2b2: x + 3 < 0
          rw [abs_of_neg (by linarith)] at hx
          by_cases h4 : x + 4 ≥ 0
          · -- Case 2b2a: x + 4 ≥ 0
            rw [abs_of_nonneg (by linarith)] at hx
            by_cases h5 : x + 5 ≥ 0
            · -- Case 2b2a1: x + 5 ≥ 0
              rw [abs_of_nonneg (by linarith)] at hx
              linarith
            · -- Case 2b2a2: x + 5 < 0
              rw [abs_of_neg (by linarith)] at hx
              linarith
          · -- Case 2b2b: x + 4 < 0
            rw [abs_of_neg (by linarith)] at hx
            by_cases h5 : x + 5 ≥ 0
            · -- Case 2b2b1: x + 5 ≥ 0
              rw [abs_of_nonneg (by linarith)] at hx
              linarith
            · -- Case 2b2b2: x + 5 < 0
              rw [abs_of_neg (by linarith)] at hx
              linarith