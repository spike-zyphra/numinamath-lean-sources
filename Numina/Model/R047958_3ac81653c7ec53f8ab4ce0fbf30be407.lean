import Mathlib

theorem number_theory_260860 (x : ℝ) (hx : ⌊x⌋ + ⌊x / 2⌋ + ⌊x / 3⌋ = 2020) :
    ⌊x / 4⌋ = 275 := by 
  let a := ⌊x⌋
  let b := ⌊x / 2⌋
  let c := ⌊x / 3⌋
  have h1 : (a : ℝ) ≤ x := by 
    exact Int.floor_le x 
  have h2 : x < (a + 1 : ℝ) := by 
    exact Int.lt_floor_add_one x 
  have h3 : (b : ℝ) ≤ x / 2 := by 
    exact Int.floor_le (x / 2)
  have h4 : x / 2 < (b + 1 : ℝ) := by 
    exact Int.lt_floor_add_one (x / 2)
  have h5 : (c : ℝ) ≤ x / 3 := by 
    exact Int.floor_le (x / 3)
  have h6 : x / 3 < (c + 1 : ℝ) := by 
    exact Int.lt_floor_add_one (x / 3)
  have h7 : (a : ℝ) + (b : ℝ) + (c : ℝ) ≤ x + x / 2 + x / 3 := by 
    linarith
  have h7' : x + x / 2 + x / 3 < (a : ℝ) + (b : ℝ) + (c : ℝ) + 3 := by 
    linarith
  rw [show (a : ℝ) + (b : ℝ) + (c : ℝ) = (2020 : ℝ) by exact_mod_cast hx] at h7 
  rw [show (a : ℝ) + (b : ℝ) + (c : ℝ) = (2020 : ℝ) by exact_mod_cast hx] at h7'
  have h8 : (2020 : ℝ) ≤ x + x / 2 + x / 3 := by linarith
  have h9 : x + x / 2 + x / 3 < (2023 : ℝ) := by
    nlinarith 
  have h12 : (2020 * 6 / 11 : ℝ) ≤ x := by
    nlinarith 
  have h13 : x < (2023 * 6 / 11 : ℝ) := by
    nlinarith 
  have h17 : (275 : ℝ) ≤ x / 4 := by
    nlinarith 
  have h18 : x / 4 < (276 : ℝ) := by
    nlinarith 
  have h16 : ⌊x / 4⌋ = 275 := by 
    rw [Int.floor_eq_iff] 
    constructor <;> (try norm_num) <;> nlinarith 
  exact h16