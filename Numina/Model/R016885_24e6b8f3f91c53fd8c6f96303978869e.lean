import Mathlib

theorem algebra_19344 : ∑ n in Finset.range 19, ⌊Real.sqrt (n + 1)⌋ = 50 := by
  have h1 : ⌊Real.sqrt (1 : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (1 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)]
  have h2 : ⌊Real.sqrt (2 : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h3 : ⌊Real.sqrt (3 : ℝ)⌋ = 1 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h4 : ⌊Real.sqrt (4 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (4 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (4 : ℝ) by norm_num)]
  have h5 : ⌊Real.sqrt (5 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h6 : ⌊Real.sqrt (6 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
  have h7 : ⌊Real.sqrt (7 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (7 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
  have h8 : ⌊Real.sqrt (8 : ℝ)⌋ = 2 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (8 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)]
  have h9 : ⌊Real.sqrt (9 : ℝ)⌋ = 3 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (9 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (9 : ℝ) by norm_num)]
  have h10 : ⌊Real.sqrt (10 : ℝ)⌋ = 3 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (10 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
  have h11 : ⌊Real.sqrt (11 : ℝ)⌋ = 3 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (11 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
  have h12 : ⌊Real.sqrt (12 : ℝ)⌋ = 3 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (12 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (12 : ℝ) by norm_num)]
  have h13 : ⌊Real.sqrt (13 : ℝ)⌋ = 3 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (13 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
  have h14 : ⌊Real.sqrt (14 : ℝ)⌋ = 3 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (14 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (14 : ℝ) by norm_num)]
  have h15 : ⌊Real.sqrt (15 : ℝ)⌋ = 3 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (15 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num)]
  have h16 : ⌊Real.sqrt (16 : ℝ)⌋ = 4 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (16 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (16 : ℝ) by norm_num)]
  have h17 : ⌊Real.sqrt (17 : ℝ)⌋ = 4 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (17 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
  have h18 : ⌊Real.sqrt (18 : ℝ)⌋ = 4 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (18 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (18 : ℝ) by norm_num)]
  have h19 : ⌊Real.sqrt (19 : ℝ)⌋ = 4 := by
    rw [Int.floor_eq_iff]
    constructor <;> (norm_num)
    <;> nlinarith [Real.sqrt_nonneg (19 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (19 : ℝ) by norm_num)]
  norm_num [Finset.sum_range_succ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]