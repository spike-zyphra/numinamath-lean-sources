import Mathlib

open Real Set

theorem algebra_277439 (a b c : ℝ) (h : a^2 + b^2 + c^2 = l) (hl : l > 0)
    (f : ℝ) (hf : f = min (min ((a - b)^2) ((b - c)^2)) ((c - a)^2)) :
    f ≤ l / 2 := by
  by_cases h1 : (a - b) ^ 2 ≤ (b - c) ^ 2
  · -- Case 1: min ((a-b)^2, (b-c)^2) = (a-b)^2
    have h2 : min ((a - b) ^ 2) ((b - c) ^ 2) = (a - b) ^ 2 := by 
      apply min_eq_left
      linarith
    have h3 : f = min ((a - b) ^ 2) ((c - a) ^ 2) := by 
      rw [hf]
      rw [h2]
    by_cases h4 : (a - b) ^ 2 ≤ (c - a) ^ 2
    · -- Case 1-1: f = (a-b)^2
      have h5 : f = (a - b) ^ 2 := by 
        rw [h3]
        apply min_eq_left
        linarith
      have h6 : (a - b) ^ 2 ≤ l / 2 := by
        nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          h, sq_nonneg (a + b + c), sq_nonneg ( (a - b) - (b - c) ), sq_nonneg ( (b - c) - (c - a) ), 
          sq_nonneg ( (c - a) - (a - b) )
        ]
      linarith [h6, h5]
    · -- Case 1-2: f = (c-a)^2
      have h5 : f = (c - a) ^ 2 := by 
        rw [h3]
        apply min_eq_right
        linarith
      have h6 : (c - a) ^ 2 ≤ l / 2 := by
        nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          h, sq_nonneg (a + b + c), sq_nonneg ( (a - b) - (b - c) ), sq_nonneg ( (b - c) - (c - a) ), 
          sq_nonneg ( (c - a) - (a - b) )
        ]
      linarith [h6, h5]
  · -- Case 2: min ((a-b)^2, (b-c)^2) = (b-c)^2
    have h2 : min ((a - b) ^ 2) ((b - c) ^ 2) = (b - c) ^ 2 := by 
      apply min_eq_right
      linarith
    have h3 : f = min ((b - c) ^ 2) ((c - a) ^ 2) := by 
      rw [hf]
      rw [h2]
    by_cases h4 : (b - c) ^ 2 ≤ (c - a) ^ 2
    · -- Case 2-1: f = (b-c)^2
      have h5 : f = (b - c) ^ 2 := by 
        rw [h3]
        apply min_eq_left 
        linarith
      have h6 : (b - c) ^ 2 ≤ l / 2 := by
        nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          h, sq_nonneg (a + b + c), sq_nonneg ( (a - b) - (b - c) ), sq_nonneg ( (b - c) - (c - a) ), 
          sq_nonneg ( (c - a) - (a - b) )
        ]
      linarith [h6, h5]
    · -- Case 2-2: f = (c-a)^2
      have h5 : f = (c - a) ^ 2 := by 
        rw [h3]
        apply min_eq_right 
        linarith
      have h6 : (c - a) ^ 2 ≤ l / 2 := by
        nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          h, sq_nonneg (a + b + c), sq_nonneg ( (a - b) - (b - c) ), sq_nonneg ( (b - c) - (c - a) ), 
          sq_nonneg ( (c - a) - (a - b) )
        ]
      linarith [h6, h5]