import Mathlib

open Real

theorem algebra_17022 : ∑ i ∈ Finset.range 16, ⌊Real.sqrt (i + 1)⌋ = 38 := by
  have h1 : ⌊Real.sqrt (1 : ℝ)⌋ = 1 := by
    have h2 : Real.sqrt (1 : ℝ) = (1 : ℝ) := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    rw [h2]
    all_goals norm_num
  have h2 : ⌊Real.sqrt (2 : ℝ)⌋ = 1 := by
    have h3 : 1 < Real.sqrt (2 : ℝ) := by
      rw [Real.lt_sqrt] <;> norm_num
    have h4 : Real.sqrt (2 : ℝ) < (2 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> linarith
  have h3 : ⌊Real.sqrt (3 : ℝ)⌋ = 1 := by
    have h3 : 1 < Real.sqrt (3 : ℝ) := by
      rw [Real.lt_sqrt] <;> norm_num
    have h4 : Real.sqrt (3 : ℝ) < (2 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> linarith
  have h4 : ⌊Real.sqrt (4 : ℝ)⌋ = 2 := by
    have h2 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    rw [h2]
    all_goals norm_num
  have h5 : ⌊Real.sqrt (5 : ℝ)⌋ = 2 := by
    have h3 : 2 ≤ Real.sqrt (5 : ℝ) := by
      have h4 : (2 : ℝ) ^ 2 ≤ (5 : ℝ) := by norm_num
      nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    have h4 : Real.sqrt (5 : ℝ) < (3 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> linarith
  have h6 : ⌊Real.sqrt (6 : ℝ)⌋ = 2 := by
    have h3 : 2 ≤ Real.sqrt (6 : ℝ) := by
      have h4 : (2 : ℝ) ^ 2 ≤ (6 : ℝ) := by norm_num
      nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
    have h4 : Real.sqrt (6 : ℝ) < (3 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> linarith
  have h7 : ⌊Real.sqrt (7 : ℝ)⌋ = 2 := by
    have h3 : 2 ≤ Real.sqrt (7 : ℝ) := by
      have h4 : (2 : ℝ) ^ 2 ≤ (7 : ℝ) := by norm_num
      nlinarith [Real.sqrt_nonneg (7 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
    have h4 : Real.sqrt (7 : ℝ) < (3 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> linarith
  have h8 : ⌊Real.sqrt (8 : ℝ)⌋ = 2 := by
    have h3 : 2 ≤ Real.sqrt (8 : ℝ) := by
      have h4 : (2 : ℝ) ^ 2 ≤ (8 : ℝ) := by norm_num
      nlinarith [Real.sqrt_nonneg (8 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)]
    have h4 : Real.sqrt (8 : ℝ) < (3 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> linarith
  have h9 : ⌊Real.sqrt (9 : ℝ)⌋ = 3 := by
    have h2 : Real.sqrt (9 : ℝ) = (3 : ℝ) := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    rw [h2]
    all_goals norm_num
  have h10 : ⌊Real.sqrt (10 : ℝ)⌋ = 3 := by
    have h3 : 3 ≤ Real.sqrt (10 : ℝ) := by
      have h4 : (3 : ℝ) ^ 2 ≤ (10 : ℝ) := by norm_num
      nlinarith [Real.sqrt_nonneg (10 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
    have h4 : Real.sqrt (10 : ℝ) < (4 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> linarith
  have h11 : ⌊Real.sqrt (11 : ℝ)⌋ = 3 := by
    have h3 : 3 ≤ Real.sqrt (11 : ℝ) := by
      have h4 : (3 : ℝ) ^ 2 ≤ (11 : ℝ) := by norm_num
      nlinarith [Real.sqrt_nonneg (11 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
    have h4 : Real.sqrt (11 : ℝ) < (4 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> linarith
  have h12 : ⌊Real.sqrt (12 : ℝ)⌋ = 3 := by
    have h3 : 3 ≤ Real.sqrt (12 : ℝ) := by
      have h4 : (3 : ℝ) ^ 2 ≤ (12 : ℝ) := by norm_num
      nlinarith [Real.sqrt_nonneg (12 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (12 : ℝ) by norm_num)]
    have h4 : Real.sqrt (12 : ℝ) < (4 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> linarith
  have h13 : ⌊Real.sqrt (13 : ℝ)⌋ = 3 := by
    have h3 : 3 ≤ Real.sqrt (13 : ℝ) := by
      have h4 : (3 : ℝ) ^ 2 ≤ (13 : ℝ) := by norm_num
      nlinarith [Real.sqrt_nonneg (13 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
    have h4 : Real.sqrt (13 : ℝ) < (4 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> linarith
  have h14 : ⌊Real.sqrt (14 : ℝ)⌋ = 3 := by
    have h3 : 3 ≤ Real.sqrt (14 : ℝ) := by
      have h4 : (3 : ℝ) ^ 2 ≤ (14 : ℝ) := by norm_num
      nlinarith [Real.sqrt_nonneg (14 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (14 : ℝ) by norm_num)]
    have h4 : Real.sqrt (14 : ℝ) < (4 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> linarith
  have h15 : ⌊Real.sqrt (15 : ℝ)⌋ = 3 := by
    have h3 : 3 ≤ Real.sqrt (15 : ℝ) := by
      have h4 : (3 : ℝ) ^ 2 ≤ (15 : ℝ) := by norm_num
      nlinarith [Real.sqrt_nonneg (15 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num)]
    have h4 : Real.sqrt (15 : ℝ) < (4 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> linarith
  have h16 : ⌊Real.sqrt (16 : ℝ)⌋ = 4 := by
    have h2 : Real.sqrt (16 : ℝ) = (4 : ℝ) := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    rw [h2]
    all_goals norm_num
  norm_num [Finset.sum_range_succ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]