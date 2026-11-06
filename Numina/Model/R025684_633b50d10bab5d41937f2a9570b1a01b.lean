import Mathlib

theorem algebra_5171 : IsGreatest {x : ℝ | 13 * x - 15 * ⌊x⌋ + 6 = 0} (129/13) := by
  constructor
  · -- Show that 129/13 is in the set
    show 13 * (129 / 13 : ℝ) - 15 * ⌊(129 / 13 : ℝ)⌋ + 6 = 0
    norm_num
  · -- Show that 129/13 is the greatest element in the set
    intro x hx
    have h : 13 * x - 15 * ⌊x⌋ + 6 = 0 := by
      simpa using hx
    let n := ⌊x⌋
    have hn1 : n ≤ (x : ℝ) := by
      exact Int.floor_le x
    have hn2 : (x : ℝ) < (n + 1 : ℝ) := by
      exact Int.lt_floor_add_one x
    have h_eq : (13 * x - 15 * (n : ℝ) + 6 : ℝ) = 0 := by
      simpa using h
    -- Rearranged: 13x + 6 = 15n
    have eq1 : (13 * x + 6 : ℝ) = (15 * (n : ℝ) : ℝ) := by
      linarith
    have hn3 : n ≥ 3 := by
      by_contra h
      push_neg at h
      have h4 : n ≤ 2 := by omega
      have h5 : (n : ℝ) ≤ (2 : ℝ) := by exact_mod_cast h4
      nlinarith [eq1, hn1]
    have hn4 : n < 10 := by
      by_contra h
      push_neg at h
      have h7 : n ≥ 10 := by omega
      have h8 : (n : ℝ) ≥ (10 : ℝ) := by exact_mod_cast h7
      nlinarith [eq1, hn2]
    have hn5 : n ≤ 9 := by omega
    have h5 : (n : ℝ) ≤ (9 : ℝ) := by exact_mod_cast hn5
    nlinarith [eq1, hn1, hn2]