import Mathlib

theorem number_theory_95018 : ∑ i ∈ Finset.range 16, ⌊Real.sqrt (i + 1)⌋ = 38 := by
  have h1 : ⌊Real.sqrt (1 : ℝ)⌋ = 1 := by 
    have h2 : Real.sqrt (1 : ℝ) = (1 : ℝ) := Real.sqrt_one
    rw [h2]
    all_goals norm_num
  have h2' : ⌊Real.sqrt (2 : ℝ)⌋ = 1 := by
    have h3 : (1 : ℝ) < Real.sqrt (2 : ℝ) := by 
      rw [Real.lt_sqrt] <;> norm_num
    have h4 : Real.sqrt (2 : ℝ) < (2 : ℝ) := by 
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  have h3' : ⌊Real.sqrt (3 : ℝ)⌋ = 1 := by 
    have h4 : (1 : ℝ) < Real.sqrt (3 : ℝ) := by 
      rw [Real.lt_sqrt] <;> norm_num
    have h5 : Real.sqrt (3 : ℝ) < (2 : ℝ) := by 
      rw [Real.sqrt_lt] <;> norm_num 
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  have h4' : ⌊Real.sqrt (4 : ℝ)⌋ = 2 := by 
    have h6 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by 
      rw [Real.sqrt_eq_cases]
      all_goals norm_num 
    rw [h6]
    all_goals norm_num
  have h5' : ⌊Real.sqrt (5 : ℝ)⌋ = 2 := by 
    have h7 : (2 : ℝ) ≤ Real.sqrt (5 : ℝ) := by 
      rw [Real.le_sqrt] <;> norm_num 
    have h8 : Real.sqrt (5 : ℝ) < (3 : ℝ) := by 
      rw [Real.sqrt_lt] <;> norm_num 
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  have h6' : ⌊Real.sqrt (6 : ℝ)⌋ = 2 := by 
    have h7 : (2 : ℝ) ≤ Real.sqrt (6 : ℝ) := by 
      rw [Real.le_sqrt] <;> norm_num 
    have h8 : Real.sqrt (6 : ℝ) < (3 : ℝ) := by 
      rw [Real.sqrt_lt] <;> norm_num 
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  have h7' : ⌊Real.sqrt (7 : ℝ)⌋ = 2 := by 
    have h8 : (2 : ℝ) ≤ Real.sqrt (7 : ℝ) := by 
      rw [Real.le_sqrt] <;> norm_num 
    have h9 : Real.sqrt (7 : ℝ) < (3 : ℝ) := by 
      rw [Real.sqrt_lt] <;> norm_num 
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  have h8' : ⌊Real.sqrt (8 : ℝ)⌋ = 2 := by 
    have h9 : (2 : ℝ) ≤ Real.sqrt (8 : ℝ) := by 
      rw [Real.le_sqrt] <;> norm_num 
    have h10 : Real.sqrt (8 : ℝ) < (3 : ℝ) := by 
      rw [Real.sqrt_lt] <;> norm_num 
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  have h9' : ⌊Real.sqrt (9 : ℝ)⌋ = 3 := by 
    have h9 : Real.sqrt (9 : ℝ) = (3 : ℝ) := by 
      rw [Real.sqrt_eq_cases] <;> norm_num 
    rw [h9]
    all_goals norm_num
  have h10' : ⌊Real.sqrt (10 : ℝ)⌋ = 3 := by 
    have h11 : (3 : ℝ) ≤ Real.sqrt (10 : ℝ) := by 
      rw [Real.le_sqrt] <;> norm_num 
    have h12 : Real.sqrt (10 : ℝ) < (4 : ℝ) := by 
      rw [Real.sqrt_lt] <;> norm_num 
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  have h11' : ⌊Real.sqrt (11 : ℝ)⌋ = 3 := by
    have h12 : (3 : ℝ) ≤ Real.sqrt (11 : ℝ) := by 
      rw [Real.le_sqrt] <;> norm_num 
    have h13 : Real.sqrt (11 : ℝ) < (4 : ℝ) := by 
      rw [Real.sqrt_lt] <;> norm_num 
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  have h12' : ⌊Real.sqrt (12 : ℝ)⌋ = 3 := by 
    have h13 : (3 : ℝ) ≤ Real.sqrt (12 : ℝ) := by
      rw [Real.le_sqrt] <;> norm_num
    have h14 : Real.sqrt (12 : ℝ) < (4 : ℝ) := by 
      rw [Real.sqrt_lt] <;> norm_num 
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  have h13' : ⌊Real.sqrt (13 : ℝ)⌋ = 3 := by 
    have h14 : (3 : ℝ) ≤ Real.sqrt (13 : ℝ) := by
      rw [Real.le_sqrt] <;> norm_num 
    have h15 : Real.sqrt (13 : ℝ) < (4 : ℝ) := by 
      rw [Real.sqrt_lt] <;> norm_num 
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  have h14' : ⌊Real.sqrt (14 : ℝ)⌋ = 3 := by 
    have h15 : (3 : ℝ) ≤ Real.sqrt (14 : ℝ) := by
      rw [Real.le_sqrt] <;> norm_num
    have h16 : Real.sqrt (14 : ℝ) < (4 : ℝ) := by 
      rw [Real.sqrt_lt] <;> norm_num 
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  have h15' : ⌊Real.sqrt (15 : ℝ)⌋ = 3 := by 
    have h16 : (3 : ℝ) ≤ Real.sqrt (15 : ℝ) := by
      rw [Real.le_sqrt] <;> norm_num 
    have h17 : Real.sqrt (15 : ℝ) < (4 : ℝ) := by
      rw [Real.sqrt_lt] <;> norm_num 
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  have h16' : ⌊Real.sqrt (16 : ℝ)⌋ = 4 := by 
    have h12 : Real.sqrt (16 : ℝ) = (4 : ℝ) := by 
      rw [Real.sqrt_eq_cases] <;> norm_num
    rw [h12] 
    all_goals norm_num
  norm_num [Finset.sum_range_succ, h1, h2', h3', h4', h5', h6', h7', h8', h9', h10', h11', h12', h13', h14', h15', h16']
  <;> norm_num