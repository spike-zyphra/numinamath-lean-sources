import Mathlib

theorem algebra_306021 {x : ℝ} (hx : x ≠ 0) (h : x + 2 * (x - ⌊x⌋) = 3 * ⌊x⌋) :
    x = 5 / 3 := by
  let n := ⌊x⌋
  have hn1 : n ≤ (x : ℝ) := by
    exact Int.floor_le x
  have hn2 : (x : ℝ) < (n + 1 : ℝ) := by
    exact Int.lt_floor_add_one x
  have eq1 : x + 2 * (x - (n : ℝ)) = 3 * (n : ℝ) := by
    simpa using h
  have eq2 : 3 * x = 5 * (n : ℝ) := by
    nlinarith
  have eq3 : (n : ℝ) ≤ x := by
    exact_mod_cast hn1
  have eq4 : x < (n + 1 : ℝ) := by
    exact_mod_cast hn2
  have h5 : (x : ℝ) = 5 / 3 * (n : ℝ) := by
    linarith
  have h5' : (n : ℝ) ≥ 0 := by
    nlinarith [h5, eq3]
  have h6' : (n : ℝ) < (3 / 2 : ℝ) := by
    nlinarith [h5, eq4]
  have hn3 : n = 0 ∨ n = 1 := by
    have hn31 : n ≥ 0 := by
      by_contra h8
      push_neg at h8
      have hn8 : n ≤ -1 := by omega
      have hn8' : (n : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast hn8
      nlinarith
    have hn32 : n < 2 := by
      by_contra h8
      push_neg at h8
      have hn8 : n ≥ 2 := by omega
      have hn8' : (n : ℝ) ≥ (2 : ℝ) := by exact_mod_cast hn8
      nlinarith
    omega
  rcases hn3 with hn3 | hn3
  · -- n = 0
    have hn4 : (n : ℝ) = (0 : ℝ) := by
      exact_mod_cast hn3
    have hx0 : x = (0 : ℝ) := by
      nlinarith [eq2, hn4]
    contradiction
  · -- n = 1
    have hn5 : (n : ℝ) = (1 : ℝ) := by
      exact_mod_cast hn3
    nlinarith [eq2, hn5]