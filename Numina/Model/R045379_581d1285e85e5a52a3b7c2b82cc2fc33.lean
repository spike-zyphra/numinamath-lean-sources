import Mathlib

theorem algebra_126289 (x : ℝ) : 20 * ⌊x⌋ - 14 * (x - ⌊x⌋) = 2014 ↔
    x = 101 + 3 / 7 := by 
  constructor
  · -- Assume 20 * ⌊x⌋ - 14 * (x - ⌊x⌋) = 2014, prove x = 101 + 3 / 7
    intro h
    let n := ⌊x⌋
    have hn1 : n ≤ (x : ℝ) := by exact Int.floor_le x
    have hn2 : (x : ℝ) < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
    have eq1 : (20 * (n : ℝ) - 14 * (x - (n : ℝ)) = (2014 : ℝ)) := by
      simpa using h
    have eq2 : (x : ℝ) = (34 * (n : ℝ) - 2014) / 14 := by
      linarith
    have h1 : (n : ℝ) ≤ (x : ℝ) := by linarith [hn1]
    have h2 : (x : ℝ) < (n + 1 : ℝ) := by linarith [hn2]
    rw [eq2] at h1
    have h3 : (n : ℝ) ≤ (34 * (n : ℝ) - 2014) / 14 := by linarith [h1]
    have h4 : n ≥ 101 := by
      by_contra h
      push_neg at h
      have hn3 : n ≤ 100 := by omega
      have h5 : (n : ℝ) ≤ (100 : ℝ) := by exact_mod_cast hn3
      nlinarith
    rw [eq2] at h2
    have h6 : (34 * (n : ℝ) - 2014) / 14 < (n + 1 : ℝ) := by linarith [h2]
    have h7 : n ≤ 101 := by
      by_contra h
      push_neg at h
      have hn8 : n ≥ 102 := by omega
      have h8 : (n : ℝ) ≥ (102 : ℝ) := by exact_mod_cast hn8
      nlinarith
    have hn_eq : n = 101 := by
      omega
    have hx_eq : x = (101 + (3 / 7 : ℝ)) := by
      rw [eq2]
      rw [show (n : ℝ) = (101 : ℝ) by exact_mod_cast hn_eq]
      norm_num
    linarith [hx_eq]
  · -- Assume x = 101 + 3/7, prove 20 * ⌊x⌋ - 14 * (x - ⌊x⌋) = 2014
    intro h
    have h1 : x = (101 + (3 / 7 : ℝ)) := by
      linarith
    have hn1 : ⌊x⌋ = 101 := by
      rw [h1]
      norm_num [Int.floor_eq_iff]
    rw [hn1]
    rw [h1]
    norm_num