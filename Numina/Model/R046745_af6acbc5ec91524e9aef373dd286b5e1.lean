import Mathlib

open Real

theorem algebra_215411 (x : ℝ) :
    2 * ⌊x⌋ = x + 2 * (x - ⌊x⌋) ↔ x = 0 ∨ x = 4 / 3 ∨ x = 8 / 3 := by
  constructor
  · -- Assume 2 * floor(x) = x + 2 * (x - floor(x)), prove x = 0 or x = 4/3 or x = 8/3
    intro h
    let n := ⌊x⌋
    have h1 : (n : ℝ) ≤ x := by exact Int.floor_le x
    have h2 : x < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
    have eq1 : (2 * (n : ℝ)) = x + 2 * (x - (n : ℝ)) := by
      simpa using h
    have eq2 : x = 4 / 3 * (n : ℝ) := by
      nlinarith
    have h3 : (n : ℝ) ≥ (0 : ℝ) := by
      nlinarith [eq2, h1]
    have h4 : (n : ℝ) < (3 : ℝ) := by
      nlinarith [eq2, h2]
    have hn1 : n ≥ 0 := by
      by_contra h'
      push_neg at h'
      have hn2 : n < 0 := by omega
      have hn2 : (n : ℝ) < (0 : ℝ) := by exact_mod_cast hn2
      nlinarith
    have hn2 : n < 3 := by
      by_contra h'
      push_neg at h'
      have hn3 : n ≥ 3 := by omega
      have hn3 : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast hn3
      nlinarith
    have hn3 : n = 0 ∨ n = 1 ∨ n = 2 := by
      omega
    rcases hn3 with (hn | hn | hn)
    · -- n = 0
      have hn0 : (n : ℝ) = (0 : ℝ) := by exact_mod_cast hn
      rw [hn0] at eq2
      left
      linarith
    · -- n = 1
      have hn1 : (n : ℝ) = (1 : ℝ) := by exact_mod_cast hn
      rw [hn1] at eq2
      right
      left
      linarith
    · -- n = 2
      have hn2 : (n : ℝ) = (2 : ℝ) := by exact_mod_cast hn
      rw [hn2] at eq2
      right
      right
      linarith
  · -- Assume x = 0 ∨ x = 4 / 3 ∨ x = 8 / 3, prove 2 * ⌊x⌋ = x + 2 * (x - ⌊x⌋)
    intro h
    rcases h with (h | h | h)
    · -- x = 0
      rw [h]
      norm_num
    · -- x = 4 / 3
      rw [h]
      norm_num
    · -- x = 8 / 3
      rw [h]
      norm_num