import Mathlib

theorem number_theory_4902 (a : ℝ) : ⌊a⌋ + ⌊a + 1 / 2⌋ = ⌊2 * a⌋ := by 
  let n := ⌊a⌋
  have h1 : n ≤ a := by exact Int.floor_le a
  have h2 : a < (n + 1 : ℝ) := by exact Int.lt_floor_add_one a
  by_cases h5 : (a - (n : ℝ)) < 1 / 2
  · -- Case 1: a - n < 1/2
    have h6 : ⌊a + (1 / 2 : ℝ)⌋ = n := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> nlinarith
    have h12 : ⌊2 * a⌋ = 2 * n := by
      have h1 : (n : ℝ) ≤ a := h1
      have h2 : a < (n + 1 : ℝ) := h2
      have h13 : (2 * n : ℝ) ≤ (2 * a : ℝ) := by 
        nlinarith
      have h14 : (2 * a : ℝ) < (2 * (n + 1) : ℝ) := by 
        linarith
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> nlinarith
    linarith [h6, h12]
  · -- Case 2: a - (n : ℝ) ≥ 1 / 2
    have h7 : ⌊a + (1 / 2 : ℝ)⌋ = n + 1 := by 
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> nlinarith
    have h8 : ⌊2 * a⌋ = 2 * n + 1 := by 
      have h1 : (n : ℝ) ≤ a := h1
      have h2 : a < (n + 1 : ℝ) := h2
      have h14 : (2 * n + 1 : ℝ) ≤ 2 * a := by 
        nlinarith
      have h15 : 2 * a < (2 * n + 2 : ℝ) := by 
        linarith
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> nlinarith
    linarith [h7, h8]