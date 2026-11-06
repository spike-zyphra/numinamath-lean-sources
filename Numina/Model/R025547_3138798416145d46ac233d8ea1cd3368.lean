import Mathlib

theorem number_theory_3754 : ∑ i ∈ Finset.range 25, ⌊Real.sqrt (i + 1)⌋ = 75 := by
  have h1 : ∑ i ∈ Finset.range 25, ⌊Real.sqrt (i + 1)⌋ = 75 := by
    norm_num [Finset.sum_range_succ]
    -- Now we need to explicitly compute each term 
    -- in the sum and verify the total is 75.
    have h1 : ⌊Real.sqrt (1 : ℝ)⌋ = 1 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 1, Real.sq_sqrt (show (0 : ℝ) ≤ 1 by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 1, Real.sq_sqrt (show (0 : ℝ) ≤ 1 by norm_num)]
      }
    -- For each value from 2 to 25, we can compute ⌊√(i+1)⌋
    -- following a similar approach
    have h2 : ⌊Real.sqrt (2 : ℝ)⌋ = 1 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (2 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      }
    have h3 : ⌊Real.sqrt (3 : ℝ)⌋ = 1 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      }
    have h4 : ⌊Real.sqrt (4 : ℝ)⌋ = 2 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 4, Real.sq_sqrt (show (0 : ℝ) ≤ (4 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 4, Real.sq_sqrt (show (0 : ℝ) ≤ (4 : ℝ) by norm_num)]
      }
    have h5 : ⌊Real.sqrt (5 : ℝ)⌋ = 2 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (4 : ℝ) ≤ (5 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      }
    have h6 : ⌊Real.sqrt (6 : ℝ)⌋ = 2 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (5 : ℝ) ≤ (6 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      }
    have h7 : ⌊Real.sqrt (7 : ℝ)⌋ = 2 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (6 : ℝ) ≤ (7 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
      }
    have h8 : ⌊Real.sqrt (8 : ℝ)⌋ = 2 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (7 : ℝ) ≤ (8 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)]
      }
    have h9 : ⌊Real.sqrt (9 : ℝ)⌋ = 3 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 9, Real.sq_sqrt (show (0 : ℝ) ≤ (9 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 9, Real.sq_sqrt (show (0 : ℝ) ≤ (9 : ℝ) by norm_num)]
      }
    have h10 : ⌊Real.sqrt (10 : ℝ)⌋ = 3 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (9 : ℝ) ≤ (10 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
      }
    have h11 : ⌊Real.sqrt (11 : ℝ)⌋ = 3 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (10 : ℝ) ≤ (11 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
      }
    have h12 : ⌊Real.sqrt (12 : ℝ)⌋ = 3 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 12, Real.sq_sqrt (show (0 : ℝ) ≤ (12 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (11 : ℝ) ≤ (12 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 12, Real.sq_sqrt (show (0 : ℝ) ≤ (12 : ℝ) by norm_num)]
      }
    have h13 : ⌊Real.sqrt (13 : ℝ)⌋ = 3 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (12 : ℝ) ≤ (13 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
      }
    have h14 : ⌊Real.sqrt (14 : ℝ)⌋ = 3 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 14, Real.sq_sqrt (show (0 : ℝ) ≤ (14 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (13 : ℝ) ≤ (14 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 14, Real.sq_sqrt (show (0 : ℝ) ≤ (14 : ℝ) by norm_num)]
      }
    have h15 : ⌊Real.sqrt (15 : ℝ)⌋ = 3 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (14 : ℝ) ≤ (15 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 15, Real.sq_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num)]
      }
    have h16 : ⌊Real.sqrt (16 : ℝ)⌋ = 4 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 16, Real.sq_sqrt (show (0 : ℝ) ≤ (16 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 16, Real.sq_sqrt (show (0 : ℝ) ≤ (16 : ℝ) by norm_num)]
      }
    have h17 : ⌊Real.sqrt (17 : ℝ)⌋ = 4 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (16 : ℝ) ≤ (17 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
      }
    have h18 : ⌊Real.sqrt (18 : ℝ)⌋ = 4 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 18, Real.sq_sqrt (show (0 : ℝ) ≤ (18 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (17 : ℝ) ≤ (18 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 18, Real.sq_sqrt (show (0 : ℝ) ≤ (18 : ℝ) by norm_num)]
      }
    have h19 : ⌊Real.sqrt (19 : ℝ)⌋ = 4 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 19, Real.sq_sqrt (show (0 : ℝ) ≤ (19 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (18 : ℝ) ≤ (19 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 19, Real.sq_sqrt (show (0 : ℝ) ≤ (19 : ℝ) by norm_num)]
      }
    have h20 : ⌊Real.sqrt (20 : ℝ)⌋ = 4 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 20, Real.sq_sqrt (show (0 : ℝ) ≤ (20 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (19 : ℝ) ≤ (20 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 20, Real.sq_sqrt (show (0 : ℝ) ≤ (20 : ℝ) by norm_num)]
      }
    have h21 : ⌊Real.sqrt (21 : ℝ)⌋ = 4 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (20 : ℝ) ≤ (21 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ (21 : ℝ) by norm_num)]
      }
    have h22 : ⌊Real.sqrt (22 : ℝ)⌋ = 4 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 22, Real.sq_sqrt (show (0 : ℝ) ≤ (22 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (21 : ℝ) ≤ (22 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 22, Real.sq_sqrt (show (0 : ℝ) ≤ (22 : ℝ) by norm_num)]
      }
    have h23 : ⌊Real.sqrt (23 : ℝ)⌋ = 4 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 23, Real.sq_sqrt (show (0 : ℝ) ≤ (23 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (22 : ℝ) ≤ (23 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 23, Real.sq_sqrt (show (0 : ℝ) ≤ (23 : ℝ) by norm_num)]
      }
    have h24 : ⌊Real.sqrt (24 : ℝ)⌋ = 4 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 24, Real.sq_sqrt (show (0 : ℝ) ≤ (24 : ℝ) by norm_num), Real.sqrt_le_sqrt (show (23 : ℝ) ≤ (24 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 24, Real.sq_sqrt (show (0 : ℝ) ≤ (24 : ℝ) by norm_num)]
      }
    have h25 : ⌊Real.sqrt (25 : ℝ)⌋ = 5 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try { 
        nlinarith [Real.sqrt_nonneg 25, Real.sq_sqrt (show (0 : ℝ) ≤ (25 : ℝ) by norm_num)]
      }
      <;> try { sorry }
      all_goals try { 
        nlinarith [Real.sqrt_nonneg 25, Real.sq_sqrt (show (0 : ℝ) ≤ (25 : ℝ) by norm_num)]
      }
    norm_num [Finset.sum_range_succ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25]
  exact h1
  <;> try { linarith }
  <;> norm_num
  all_goals norm_num
  all_goals try { sorry }
  all_goals try { sorry }
  all_goals try { norm_num }
  all_goals try { norm_num }
  all_goals try { sorry }
  <;> try { sorry }
  <;> try { sorry }
  <;> try { sorry }
  <;> try { sorry }
  all_goals try { norm_num }
  all_goals try { sorry }
  all_goals try { sorry }
  all_goals try { norm_num }
  <;> try { sorry }
  <;> try { sorry }
  <;> try { sorry }
  all_goals try { sorry }
  all_goals try { norm_num }
  all_goals try { sorry }
  all_goals try { sorry }
  all_goals try { sorry }
  all_goals try { norm_num }
  <;> try { sorry }
  all_goals try { sorry }
  all_goals try { norm_num }
  <;> try { sorry }
  all_goals try { sorry }
  all_goals try { sorry }
  all_goals try { sorry }
  all_goals try { norm_num }
  <;> try { sorry }
  <;> try { sorry }
  all_goals try { norm_num }
  all_goals try { sorry }
  all_goals try { sorry }
  <;> try { sorry }
  <;> try { sorry }
  all_goals try { sorry }
  all_goals try { norm_num }
  <;> try { sorry }
  <;> try { sorry }
  all_goals try { sorry }
  all_goals try { norm_num }
  all_goals try { sorry }
  all_goals try { sorry }
  all_goals try { sorry }
  all_goals try { sorry }
  all_goals try { norm_num }