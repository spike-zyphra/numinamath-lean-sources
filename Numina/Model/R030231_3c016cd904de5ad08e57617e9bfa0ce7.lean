import Mathlib
theorem algebra_112955 (x : ℝ) (hx : x^2 + 2 * ⌊x⌋ * (x - ⌊x⌋) + 3 * (x - ⌊x⌋)^2 = 4) :
    x = -5 / 2 ∨ x = -2 ∨ x = 2 ∨ x = 3 / 2 := by 
  let n := ⌊x⌋
  have hn1 : n ≤ (x : ℝ) := by exact Int.floor_le x
  have hn2 : (x : ℝ) < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x

  have h_eq : 4 * x ^ 2 - 4 * x * (n : ℝ) + (n : ℝ) ^ 2 = 4 := by 
    nlinarith [hx]

  have h_eq2 : (2 * x - (n : ℝ)) ^ 2 = 4 := by 
    nlinarith

  have h_eq3 : 2 * x - (n : ℝ) = 2 ∨ 2 * x - (n : ℝ) = -2 := by 
    have h : (2 * x - (n : ℝ)) ^ 2 = 4 := h_eq2
    have : 2 * x - (n : ℝ) = 2 ∨ 2 * x - (n : ℝ) = -2 := by
      have h1 : (2 * x - (n : ℝ) - 2) * (2 * x - (n : ℝ) + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h1) with h2 h3
      · left
        linarith
      · right
        linarith
    assumption

  cases h_eq3 with
  | inl h1 =>
    have h2 : (x : ℝ) = (n + 2 : ℝ) / 2 := by
      linarith

    have hn3 : n > 0 := by
      by_contra h
      push_neg at h 
      have hn3 : n ≤ 0 := by omega
      have hn4 : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast hn3
      nlinarith [h2, hn1, hn2, hn4]

    have hn4 : n ≤ 2 := by
      by_contra h
      push_neg at h
      have hn5 : n ≥ 3 := by omega
      have hn6 : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast hn5
      nlinarith [h2, hn1, hn2, hn6]

    have hn5 : n = 1 ∨ n = 2 := by omega

    cases hn5 with 
    | inl h6 =>
      have hx1 : x = (3 : ℝ) / 2 := by 
        have h7 : n = 1 := h6
        have h8 : (n : ℝ) = 1 := by exact_mod_cast h7
        linarith [h2, h8]
      right
      right
      right
      linarith

    | inr h7 =>
      have hx2 : x = (2 : ℝ) := by 
        have h7 : n = 2 := h7
        have h8 : (n : ℝ) = 2 := by exact_mod_cast h7
        linarith [h2, h8]
      right 
      right
      left
      linarith

  | inr h1 =>
    have h2 : (x : ℝ) = (n - 2 : ℝ) / 2 := by 
      linarith

    have hn3 : n ≤ -2 := by
      by_contra h 
      push_neg at h 
      have hn5 : n ≥ -1 := by omega 
      have hn6 : (n : ℝ) ≥ (-1 : ℝ) := by exact_mod_cast hn5
      nlinarith [h2, hn1, hn2, hn6]

    have hn4 : n > -4 := by
      by_contra h 
      push_neg at h
      have hn5 : n ≤ -4 := by omega
      have hn6 : (n : ℝ) ≤ (-4 : ℝ) := by exact_mod_cast hn5
      nlinarith [h2, hn1, hn2, hn6]

    have hn5 : n = -3 ∨ n = -2 := by omega

    cases hn5 with
    | inl h6 =>
      have hx1 : x = (-5 : ℝ) / 2 := by
        have h7 : n = -3 := h6
        have h8 : (n : ℝ) = (-3 : ℝ) := by exact_mod_cast h7
        linarith [h2, h8]

      left
      linarith

    | inr h7 =>
      have hx2 : x = (-2 : ℝ) := by 
        have h7 : n = -2 := h7
        have h8 : (n : ℝ) = (-2 : ℝ) := by exact_mod_cast h7
        linarith [h2, h8]
      right
      left
      linarith