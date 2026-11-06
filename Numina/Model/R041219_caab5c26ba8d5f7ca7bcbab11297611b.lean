import Mathlib

theorem number_theory_206216 (x : ℝ) : ⌊x⌋ + ⌊x + 1 / 2⌋ = ⌊2 * x⌋ := by 
  let n := ⌊x⌋
  have h1 : (n : ℝ) ≤ x := by exact Int.floor_le x
  have h2 : x < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
  
  -- Now we consider two cases based on the value of x
  by_cases h : x < n + 1 / 2
  · -- Case 1: x < n + 1/2
    have h3 : ⌊x + 1 / 2⌋ = n := by
      have h4 : (n : ℝ) ≤ x + 1 / 2 := by nlinarith
      have h5 : x + 1 / 2 < (n + 1 : ℝ) := by nlinarith
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> (try linarith)
    have h6 : ⌊2 * x⌋ = 2 * n := by
      have h7 : (2 * n : ℝ) ≤ 2 * x := by nlinarith
      have h8 : 2 * x < (2 * n + 1 : ℝ) := by nlinarith
      have h9 : ⌊2 * x⌋ = 2 * n := by
        have h10 : (2 * n : ℝ) ≤ 2 * x := by nlinarith
        have h11 : 2 * x < (2 * n + 1 : ℝ) := by nlinarith
        have h12 : ⌊2 * x⌋ = 2 * n := by
          rw [Int.floor_eq_iff]
          constructor <;> (try norm_num) <;> (try linarith)
        omega
      omega
    omega
  · -- Case 2: x ≥ n + 1/2
    have h4 : ⌊x + 1 / 2⌋ = n + 1 := by
      have h5 : (n + 1 : ℝ) ≤ x + 1 / 2 := by nlinarith 
      have h6 : x + 1 / 2 < (n + 2 : ℝ) := by nlinarith 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> (try linarith)
    have h7 : ⌊2 * x⌋ = 2 * n + 1 := by
      have h8 : (2 * n + 1 : ℝ) ≤ 2 * x := by nlinarith 
      have h9 : 2 * x < (2 * n + 2 : ℝ) := by nlinarith 
      have h10 : ⌊2 * x⌋ = 2 * n + 1 := by
        have h11 : (2 * n + 1 : ℝ) ≤ 2 * x := by nlinarith 
        have h12 : 2 * x < (2 * n + 2 : ℝ) := by nlinarith 
        have h13 : ⌊2 * x⌋ = 2 * n + 1 := by
          rw [Int.floor_eq_iff]
          constructor <;> (try norm_num) <;> (try linarith)
        omega
      omega
    omega