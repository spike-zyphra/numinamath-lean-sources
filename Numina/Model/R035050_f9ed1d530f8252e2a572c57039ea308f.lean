import Mathlib

theorem algebra_268292 (x : ℝ) (hx : x^2 - 8 * ⌊x⌋ + 7 = 0) :
    x = 1 ∨ x = Real.sqrt 33 ∨ x = Real.sqrt 41 ∨ x = 7 := by
  let n := ⌊x⌋
  have hn1 : (n : ℝ) ≤ (x : ℝ) := by exact Int.floor_le x
  have hn2 : (x : ℝ) < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
  have h_eq : (x : ℝ)^2 = (8 * (n : ℝ) - 7) := by
    have h1 : (x: ℝ) ^2 - 8 * (n: ℝ) + 7 = 0 := by
      exact_mod_cast hx
    linarith
  have h3 : n ≥ 1 := by
    by_contra h
    push_neg at h
    have hn3 : n ≤ 0 := by omega
    have hn4 : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hn3
    nlinarith [h_eq, hn4, hn1, hn2, sq_nonneg (x : ℝ)]
  have h4 : n ≤ 7 := by
    by_contra h
    push_neg at h
    have hn4 : n ≥ 8 := by omega
    have hn5 : (n : ℝ) ≥ (8 : ℝ) := by exact_mod_cast hn4
    nlinarith [sq_nonneg (x - (n : ℝ)), h_eq, hn1, hn2, sq_nonneg (x + (n : ℝ))]
  have hn5 : n ≤ 7 := h4
  have hn6 : n ≥ 1 := h3
  have h7 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by
    omega
  rcases h7 with (h7 | h7 | h7 | h7 | h7 | h7 | h7)
  · -- n = 1
    have hn8 : (n : ℝ) = (1 : ℝ) := by exact_mod_cast h7
    rw [hn8] at h_eq
    have h10 : (x : ℝ) ^ 2 = (1 : ℝ) := by linarith
    have h11 : x = 1 := by
      nlinarith
    left
    linarith
  · -- n = 2
    have hn8 : (n : ℝ) = (2 : ℝ) := by exact_mod_cast h7
    rw [hn8] at h_eq
    have h10 : (x : ℝ) ^ 2 = (9 : ℝ) := by linarith
    nlinarith
  · -- n = 3
    have hn8 : (n : ℝ) = (3 : ℝ) := by exact_mod_cast h7
    rw [hn8] at h_eq
    have h10 : (x : ℝ) ^ 2 = (17 : ℝ) := by linarith
    nlinarith [sq_nonneg (x - 4 : ℝ), sq_nonneg (x + 4 : ℝ)]
  · -- n = 4
    have hn8 : (n : ℝ) = (4 : ℝ) := by exact_mod_cast h7
    rw [hn8] at h_eq
    have h10 : (x : ℝ) ^ 2 = (25 : ℝ) := by linarith
    nlinarith [sq_nonneg (x - 5 : ℝ), sq_nonneg (x + 5 : ℝ)]
  · -- n = 5
    have hn8 : (n : ℝ) = (5 : ℝ) := by exact_mod_cast h7
    rw [hn8] at h_eq
    have h12 : (x : ℝ) ^ 2 = (33 : ℝ) := by linarith
    have h13 : x ≥ (0 : ℝ) := by
      nlinarith [h12, hn1, hn2]
    have h14 : x = Real.sqrt 33 := by
      have : x ≥ 0 := h13
      have h15 : (x : ℝ) ^ 2 = (33 : ℝ) := h12
      have h16 : (Real.sqrt 33 : ℝ) ^ 2 = (33 : ℝ) := Real.sq_sqrt (by norm_num)
      have h17 : x = Real.sqrt 33 := by nlinarith [h15, h16, Real.sqrt_nonneg 33]
      exact h17
    right
    left
    linarith
  · -- n = 6
    have hn8 : (n : ℝ) = (6 : ℝ) := by exact_mod_cast h7
    rw [hn8] at h_eq
    have h12 : (x : ℝ) ^ 2 = (41 : ℝ) := by linarith
    have h13 : x ≥ (0 : ℝ) := by
      nlinarith [h12, hn1, hn2]
    have h14 : x = Real.sqrt 41 := by
      have : x ≥ 0 := h13
      have h15 : (x : ℝ) ^ 2 = (41 : ℝ) := h12
      have h16 : (Real.sqrt 41 : ℝ) ^ 2 = (41 : ℝ) := Real.sq_sqrt (by norm_num)
      have h17 : x = Real.sqrt 41 := by nlinarith [h15, h16, Real.sqrt_nonneg 41]
      exact h17
    right
    right
    left
    linarith
  · -- n = 7
    have hn8 : (n : ℝ) = (7 : ℝ) := by exact_mod_cast h7
    rw [hn8] at h_eq
    have h14 : (x : ℝ) ^ 2 = (49 : ℝ) := by linarith
    have h12 : x = (7 : ℝ) := by
      nlinarith
    right
    right
    right
    linarith