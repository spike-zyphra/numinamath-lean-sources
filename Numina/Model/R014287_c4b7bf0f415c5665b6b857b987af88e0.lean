import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_184084 :
  IsLeast {∑ i in Finset.range 10, |x - (i+1)^2| | x : ℝ} 275 := by
    constructor
    · -- Show 275 is in the set
      use 25
      norm_num [Finset.sum_range_succ]
      <;> norm_num [abs]
      <;> norm_num
    · -- Show 275 is the least
      intro s hs
      rcases hs with ⟨x, hx⟩
      have h1 : ∑ i in Finset.range 10, |x - (i + 1) ^ 2| = s := by
        simpa using hx
      have h2 : ∑ i in Finset.range 10, |x - (i + 1) ^ 2| ≥ 275 := by
        have h3 : |x - (0 + 1 : ℝ) ^ 2| + |x - (1 + 1 : ℝ) ^ 2| + |x - (2 + 1 : ℝ) ^ 2| + |x - (3 + 1 : ℝ) ^ 2| + |x - (4 + 1 : ℝ) ^ 2| + |x - (5 + 1 : ℝ) ^ 2| + |x - (6 + 1 : ℝ) ^ 2| + |x - (7 + 1 : ℝ) ^ 2| + |x - (8 + 1 : ℝ) ^ 2| + |x - (9 + 1 : ℝ) ^ 2| ≥ 275 := by
          have h4 : |x - (0 + 1 : ℝ) ^ 2| + |x - (9 + 1 : ℝ) ^ 2| ≥ 99 := by
            have h5 : |x - (0 + 1 : ℝ) ^ 2| + |x - (9 + 1 : ℝ) ^ 2| ≥ |(x - (0 + 1 : ℝ) ^ 2) - (x - (9 + 1 : ℝ) ^ 2)| := by
              apply abs_sub
            have h6 : (x - (0 + 1 : ℝ) ^ 2) - (x - (9 + 1 : ℝ) ^ 2) = 99 := by
              norm_num
              <;> linarith
            rw [h6] at h5
            norm_num at h5 ⊢
            linarith
          have h5 : |x - (1 + 1 : ℝ) ^ 2| + |x - (8 + 1 : ℝ) ^ 2| ≥ 77 := by
            have h5 : |x - (1 + 1 : ℝ) ^ 2| + |x - (8 + 1 : ℝ) ^ 2| ≥ |(x - (1 + 1 : ℝ) ^ 2) - (x - (8 + 1 : ℝ) ^ 2)| := by
              apply abs_sub
            have h6 : (x - (1 + 1 : ℝ) ^ 2) - (x - (8 + 1 : ℝ) ^ 2) = 77 := by
              norm_num
              <;> linarith
            rw [h6] at h5
            norm_num at h5 ⊢
            linarith
          have h6 : |x - (2 + 1 : ℝ) ^ 2| + |x - (7 + 1 : ℝ) ^ 2| ≥ 55 := by
            have h5 : |x - (2 + 1 : ℝ) ^ 2| + |x - (7 + 1 : ℝ) ^ 2| ≥ |(x - (2 + 1 : ℝ) ^ 2) - (x - (7 + 1 : ℝ) ^ 2)| := by
              apply abs_sub
            have h6 : (x - (2 + 1 : ℝ) ^ 2) - (x - (7 + 1 : ℝ) ^ 2) = 55 := by
              norm_num
              <;> linarith
            rw [h6] at h5
            norm_num at h5 ⊢
            linarith
          have h7 : |x - (3 + 1 : ℝ) ^ 2| + |x - (6 + 1 : ℝ) ^ 2| ≥ 33 := by
            have h5 : |x - (3 + 1 : ℝ) ^ 2| + |x - (6 + 1 : ℝ) ^ 2| ≥ |(x - (3 + 1 : ℝ) ^ 2) - (x - (6 + 1 : ℝ) ^ 2)| := by
              apply abs_sub
            have h6 : (x - (3 + 1 : ℝ) ^ 2) - (x - (6 + 1 : ℝ) ^ 2) = 33 := by
              norm_num
              <;> linarith
            rw [h6] at h5
            norm_num at h5 ⊢
            linarith
          have h8 : |x - (4 + 1 : ℝ) ^ 2| + |x - (5 + 1 : ℝ) ^ 2| ≥ 11 := by
            have h5 : |x - (4 + 1 : ℝ) ^ 2| + |x - (5 + 1 : ℝ) ^ 2| ≥ |(x - (4 + 1 : ℝ) ^ 2) - (x - (5 + 1 : ℝ) ^ 2)| := by
              apply abs_sub
            have h6 : (x - (4 + 1 : ℝ) ^ 2) - (x - (5 + 1 : ℝ) ^ 2) = 11 := by
              norm_num
              <;> linarith
            rw [h6] at h5
            norm_num at h5 ⊢
            linarith
          linarith [h4, h5, h6, h7, h8]
        have h00 : ∑ i in Finset.range 10, |x - (i + 1) ^ 2| = |x - (0 + 1 : ℝ) ^ 2| + |x - (1 + 1 : ℝ) ^ 2| + |x - (2 + 1 : ℝ) ^ 2| + |x - (3 + 1 : ℝ) ^ 2| + |x - (4 + 1 : ℝ) ^ 2| + |x - (5 + 1 : ℝ) ^ 2| + |x - (6 + 1 : ℝ) ^ 2| + |x - (7 + 1 : ℝ) ^ 2| + |x - (8 + 1 : ℝ) ^ 2| + |x - (9 + 1 : ℝ) ^ 2| := by 
          simp [Finset.sum_range_succ]
          <;> ring_nf <;> norm_num
        linarith [h00, h3]
      have h3 : s ≥ 275 := by
        linarith [h1, h2]
      linarith [h3]