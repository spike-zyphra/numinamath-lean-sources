import Mathlib

theorem algebra_81187 (x : ℝ) : x - ⌊x / 2016⌋ = 2016 ↔ x = 2017 := by
  constructor
  · -- Forward: if x - ⌊x / 2016⌋ = 2016, then x = 2017
    intro h
    let n := ⌊x / 2016⌋
    have hn1 : (n : ℝ) ≤ x / 2016 := by exact Int.floor_le (x / 2016)
    have hn2 : x / 2016 < (n + 1 : ℝ) := by exact Int.lt_floor_add_one (x / 2016)
    have heq : x = 2016 + (n : ℝ) := by
      have h_eq : (x : ℝ) - (n : ℝ) = 2016 := by
        simpa using h
      linarith
    have h1 : (n : ℝ) ≤ x / 2016 := hn1
    have h2 : x / 2016 < (n + 1 : ℝ) := hn2
    rw [show x = 2016 + (n : ℝ) by linarith [heq]] at h1 h2
    have h3 : (n : ℝ) ≤ (2016 + (n : ℝ)) / 2016 := by linarith
    have h4 : (2016 + (n : ℝ)) / 2016 < (n + 1 : ℝ) := by linarith
    have h5 : (n : ℝ) * 2016 ≤ 2016 + (n : ℝ) := by
      have h5 : (n : ℝ) ≤ (2016 + (n : ℝ)) / 2016 := h3
      have h6 : (n : ℝ) * 2016 ≤ 2016 + (n : ℝ) := by
        norm_num at h5 ⊢
        linarith
      linarith
    have h6 : 2016 + (n : ℝ) < (n + 1 : ℝ) * 2016 := by
      have h4' : (2016 + (n : ℝ)) / 2016 < (n + 1 : ℝ) := h4
      have h7 : 2016 + (n : ℝ) < (n + 1 : ℝ) * 2016 := by
        norm_num at h4' ⊢
        linarith
      linarith
    have hn3 : n ≤ 1 := by
      by_contra h7
      push_neg at h7
      have hn4 : n ≥ 2 := by omega
      have hn5 : (n : ℝ) ≥ (2 : ℝ) := by exact_mod_cast hn4
      nlinarith
    have hn4 : n ≥ 1 := by
      by_contra h7
      push_neg at h7
      have hn5 : n ≤ 0 := by omega
      have hn6 : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hn5
      nlinarith
    have hn5 : n = 1 := by
      omega
    have hx1 : x = 2017 := by
      rw [show (n : ℝ) = (1 : ℝ) by exact_mod_cast hn5] at heq
      linarith
    assumption
  · -- Backward: if x = 2017, prove x - ⌊x / 2016⌋ = 2016
    intro h_eq
    rw [h_eq]
    norm_num -- calculates the arithmetic with exact real precision
    all_goals norm_num
    all_goals norm_num
    all_goals norm_num