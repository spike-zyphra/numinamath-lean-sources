import Mathlib

theorem algebra_168773 (a : ℝ) (h : ⌊5 * a - 0.9⌋ = 3 * a + 0.7) : a = 1.1 := by
  let n := ⌊5 * a - 0.9⌋
  have h1 : n ≤ 5 * a - 0.9 := by
    exact Int.floor_le (5 * a - 0.9)
  have h2 : 5 * a - 0.9 < (n + 1 : ℝ) := by
    exact Int.lt_floor_add_one (5 * a - 0.9)
  have h3 : (n : ℝ) = 3 * a + 0.7 := by
    exact_mod_cast h
  have h4 : (n : ℝ) ≤ 5 * a - 0.9 := by
    exact_mod_cast h1
  have h5 : 5 * a - 0.9 < (n + 1 : ℝ) := by
    exact_mod_cast h2
  have h11 : n = 4 := by
    have hn1 : n ≤ 4 := by
      by_contra h
      push_neg at h
      have hn2 : n ≥ 5 := by
        omega
      have hn3 : (n : ℝ) ≥ (5 : ℝ) := by
        exact_mod_cast hn2
      nlinarith
    have hn2 : n ≥ 4 := by
      by_contra h
      push_neg at h
      have hn3 : n ≤ 3 := by
        omega
      have hn4 : (n : ℝ) ≤ (3 : ℝ) := by
        exact_mod_cast hn3
      nlinarith
    omega
  have h12 : a = 1.1 := by
    have hn12 : (n : ℝ) = 4 := by
      exact_mod_cast h11
    nlinarith
  linarith