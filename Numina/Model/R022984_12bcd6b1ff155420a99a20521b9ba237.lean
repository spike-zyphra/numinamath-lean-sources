import Mathlib

theorem algebra_267955 (x : ℝ) (hx : x^2 - 4 * ⌊x⌋ + 3 = 0) :
    x = 3 ∨ x = Real.sqrt 5 ∨ x = 1 := by
  let n := ⌊x⌋
  have hn1 : n ≤ (x : ℝ) := by exact Int.floor_le x
  have hn2 : (x : ℝ) < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
  have h_eq : x^2 - 4 * (n : ℝ) + 3 = 0 := by
    simpa using hx
  have h1 : (n : ℝ) ≤ x := by exact_mod_cast hn1
  have h2 : x < (n + 1 : ℝ) := by exact_mod_cast hn2
  have eq1 : x^2 = 4 * (n : ℝ) - 3 := by
    linarith
  have h3 : n ≥ 1 := by
    by_contra h
    push_neg at h
    have hn3 : n ≤ 0 := by linarith
    have hn4 : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hn3
    nlinarith [sq_nonneg x]
  have h4 : n ≤ 3 := by
    by_contra h
    push_neg at h
    have hn5 : n ≥ 4 := by linarith
    have hn6 : (n : ℝ) ≥ (4 : ℝ) := by exact_mod_cast hn5
    nlinarith [sq_nonneg (x - (n : ℝ)), sq_nonneg (x), sq_nonneg ((n : ℝ) - 4), Real.sqrt_nonneg (0 : ℝ)]
  have h5 : n = 1 ∨ n = 2 ∨ n = 3 := by
    interval_cases n <;> omega
  rcases h5 with h5 | h5 | h5
  · -- Case n = 1
    have hn11 : (n : ℝ) = (1 : ℝ) := by exact_mod_cast h5
    have h_eq1 : x^2 = (1 : ℝ) := by
      rw [hn11] at eq1
      nlinarith
    have h6 : x = 1 ∨ x = -1 := by
      have h7 : x^2 - (1 : ℝ) = 0 := by linarith
      have h8 : (x - 1) * (x + 1) = 0 := by
        linarith [h7]
      cases' (mul_eq_zero.1 h8) with h9 h10
      · left
        linarith
      · right
        linarith
    cases' h6 with h6 h6
    · -- x = 1
      right
      right
      norm_num [h6]
    · -- x = -1
      nlinarith
  · -- Case n = 2
    have hn22 : (n : ℝ) = (2 : ℝ) := by exact_mod_cast h5
    have h_eq2 : x^2 = (5 : ℝ) := by
      rw [hn22] at eq1
      nlinarith
    have h11 : x = Real.sqrt 5 ∨ x = -Real.sqrt 5 := by
      have h13 : x^2 = (5 : ℝ) := h_eq2
      have h21 : x = Real.sqrt (5 : ℝ) ∨ x = -Real.sqrt (5 : ℝ) := by
        have h22 : x^2 - (5 : ℝ) = 0 := by linarith
        have h23 : (x - Real.sqrt (5 : ℝ)) * (x + Real.sqrt (5 : ℝ)) = 0 := by
          nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        cases' (mul_eq_zero.1 h23) with h24 h25
        · left
          linarith
        · right
          linarith
      tauto
    cases' h11 with h11 h11
    · -- x = sqrt(5)
      right
      left
      exact h11
    · -- x = -sqrt(5)
      nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (0 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  · -- Case n = 3
    have hn33 : (n : ℝ) = (3 : ℝ) := by exact_mod_cast h5
    have h_eq3 : x^2 = (9 : ℝ) := by
      rw [hn33] at eq1
      nlinarith
    have h20 : x = 3 ∨ x = -3 := by
      have h23 : x^2 - (9 : ℝ) = 0 := by linarith
      have h24 : (x - 3) * (x + 3) = 0 := by
        linarith [h23]
      cases' (mul_eq_zero.1 h24) with h25 h26
      · left
        linarith
      · right
        linarith
    cases' h20 with h20 h20
    · -- x = 3
      left
      norm_num [h20]
    · -- x = -3
      nlinarith