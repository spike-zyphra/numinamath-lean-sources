import Mathlib

theorem algebra_177353 {x : ℝ} (hx : ⌊(10 + 3 * x) / 6⌋ = (5 * x + 3) / 7) :
    x = 11 / 5 ∨ x = 18 / 5 ∨ x = 5 := by

  let n := ⌊(10 + 3 * x) / 6⌋

  have h1 : (n : ℝ) ≤ (10 + 3 * x) / 6 := by
    exact Int.floor_le ( (10 + 3 * x) / 6 )
  have h2 : (10 + 3 * x) / 6 < (n + 1 : ℝ) := by
    exact Int.lt_floor_add_one ( (10 + 3 * x) / 6 )
  have h3 : (n : ℝ) = (5 * x + 3) / 7 := by
    exact_mod_cast hx

  have h4 : (5 * x + 3) / 7 ≤ (10 + 3 * x) / 6 := by
    nlinarith [ h1, h3 ]
  have h5 : (10 + 3 * x) / 6 < (5 * x + 3) / 7 + 1 := by
    nlinarith [ h2, h3 ]

  have h6 : n = 2 ∨ n = 3 ∨ n = 4 := by
    have h7 : n ≥ 2 := by
      by_contra h
      push_neg at h
      have h8 : n ≤ 1 := by
        omega
      have h9 : (n : ℝ) ≤ (1 : ℝ) := by
        exact_mod_cast h8
      nlinarith
    have h8 : n ≤ 4 := by
      by_contra h
      push_neg at h
      have h9 : n ≥ 5 := by
        omega
      have h10 : (n : ℝ) ≥ (5 : ℝ) := by
        exact_mod_cast h9
      nlinarith
    omega
  rcases h6 with h6 | h6 | h6
  · -- n = 2
    have h_n2 : (n : ℝ) = (2 : ℝ) := by
      exact_mod_cast h6
    have h7 : (5 * x + 3) / 7 = (2 : ℝ) := by 
      linarith [h3, h_n2]
    left
    linarith
  · -- n = 3
    have h_n3 : (n : ℝ) = (3 : ℝ) := by
      exact_mod_cast h6
    have h8 : (5 * x + 3) / 7 = (3 : ℝ) := by 
      linarith [h3, h_n3]
    right
    left
    linarith
  · -- n = 4
    have h_n4 : (n : ℝ) = (4 : ℝ) := by
      exact_mod_cast h6
    have h9 : (5 * x + 3) / 7 = (4 : ℝ) := by 
      linarith [h3, h_n4]
    right
    right
    linarith