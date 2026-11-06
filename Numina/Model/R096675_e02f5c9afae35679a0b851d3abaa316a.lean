import Mathlib

theorem number_theory_5974 (x : ℝ) : ⌊x⌋ + ⌊x + 1 / 2⌋ = ⌊2 * x⌋ := by 
  let n := ⌊x⌋
  have hn1 : n ≤ (x : ℝ) := by exact Int.floor_le x
  have hn2 : (n + 1 : ℝ) > x := by exact Int.lt_floor_add_one x
  by_cases h : (x : ℝ) - (n : ℝ) < 1 / 2
  · -- case $r < 1 / 2$ 
    have h1 : ⌊x + 1 / 2⌋ = n := by
      have h2 : x + 1 / 2 < (n + 1 : ℝ) := by linarith
      have h3 : (n : ℝ) ≤ x + 1 / 2 := by linarith
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try linarith
    have h4 : ⌊2 * x⌋ = 2 * n := by
      have h5 : 2 * x < (2 * (n : ℝ) + 1 : ℝ) := by
        linarith [show (x : ℝ) < (n + 1 : ℝ) from by linarith, h]
      have h6 : (2 * (n : ℝ) : ℝ) ≤ 2 * x := by
        nlinarith
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try linarith
    linarith [h1, h4]
  · -- case $r \geq 1 / 2$
    have h1 : ⌊x + 1 / 2⌋ = n + 1 := by
      have h2 : x + 1 / 2 ≥ (n + 1 : ℝ) := by
        linarith
      have h3 : x + 1 / 2 < (n + 2 : ℝ) := by
        linarith [show (x : ℝ) < (n + 1 : ℝ) from by linarith]
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try linarith
    have h4 : ⌊2 * x⌋ = 2 * n + 1 := by
      have h5 : 2 * x >= (2 * (n : ℝ) + 1 : ℝ) := by
        nlinarith
      have h6 : 2 * x < (2 * (n : ℝ) + 2 : ℝ) := by
        linarith [show (x : ℝ) < (n + 1 : ℝ) from by linarith]
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> try linarith
      all_goals nlinarith
    linarith [h1, h4]