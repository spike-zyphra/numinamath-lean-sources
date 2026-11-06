import Mathlib

theorem number_theory_7097 (x : ℝ) : x - ⌊x / 2016⌋ = 2016 ↔ x = 2017 := by
  constructor
  · -- Forward direction: x - ⌊x / 2016⌋ = 2016 → x = 2017
    intro h
    let n := ⌊x / 2016⌋
    have h1 : (n : ℝ) ≤ x / 2016 := by exact Int.floor_le (x / 2016)
    have h2 : x / 2016 < (n + 1 : ℝ) := by exact Int.lt_floor_add_one (x / 2016)
    have h3 : x = 2016 + (n : ℝ) := by
      have eq1 : (x : ℝ) - (n : ℝ) = 2016 := by
        simpa using h
      linarith
    have h4 : (n : ℝ) ≤ (2016 + (n : ℝ)) / 2016 := by
      have h41 : (n : ℝ) ≤ x / 2016 := by exact_mod_cast h1
      rw [h3] at h41
      linarith
    have h5 : (2016 + (n : ℝ)) / 2016 < (n + 1 : ℝ) := by
      have h51 : x / 2016 < (n + 1 : ℝ) := by exact_mod_cast h2
      rw [h3] at h51
      linarith
    have hn1 : n ≤ 1 := by
      by_contra h6
      push_neg at h6
      have hn2 : n ≥ 2 := by omega
      have hn2' : (n : ℝ) ≥ (2 : ℝ) := by exact_mod_cast hn2
      nlinarith
    have hn2 : n > 0 := by
      by_contra h6
      push_neg at h6
      have hn3 : n ≤ 0 := by omega
      have hn3' : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hn3
      nlinarith
    have hn3 : n = 1 := by
      omega
    have h6 : x = (2017 : ℝ) := by
      rw [h3]
      have hn4 : (n : ℝ) = (1 : ℝ) := by
        exact_mod_cast hn3
      linarith
    linarith
  · -- Backward direction: x = 2017 → x - ⌊x / 2016⌋ = 2016
    intro h
    rw [h]
    norm_num
    <;> try { tauto }
    all_goals norm_num