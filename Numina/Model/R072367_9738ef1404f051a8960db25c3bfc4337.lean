import Mathlib

theorem algebra_224848 {x : ℝ} (hx : ⌊(25 * x - 2) / 4⌋ = (13 * x + 4) / 3) :
    x = 14 / 13 ∨ x = 17 / 13 := by
  let n := ⌊(25 * x - 2) / 4⌋
  have h1 : (n : ℝ) = (13 * x + 4) / 3 := by
    exact_mod_cast hx
  have h2 : (n : ℝ) ≤ (25 * x - 2) / 4 := by
    apply Int.floor_le
  have h3 : (25 * x - 2) / 4 < (n + 1 : ℝ) := by
    apply Int.lt_floor_add_one
  have eq1 : (13 : ℝ) * x = 3 * (n : ℝ) - 4 := by 
    nlinarith
  have h7 : n ≥ 6 := by 
    by_contra h
    push_neg at h
    have : n ≤ 5 := by
      omega
    have hn3 : (n : ℝ) ≤ (5 : ℝ) := by 
      exact_mod_cast this
    nlinarith [h2, eq1]
  have h9 : n ≤ 7 := by 
    by_contra h
    push_neg at h
    have : n ≥ 8 := by 
      omega
    have hn3 : (n : ℝ) ≥ (8 : ℝ) := by 
      exact_mod_cast this
    nlinarith [h3, eq1]
  have h10 : n = 6 ∨ n = 7 := by 
    omega
  cases h10 with
  | inl hn6 =>
    have h8 : (n : ℝ) = (6 : ℝ) := by 
      exact_mod_cast hn6
    have h9 : x = (14 : ℝ) / 13 := by 
      nlinarith [h1, h8]
    left
    linarith
  | inr hn7 =>
    have h8 : (n : ℝ) = (7 : ℝ) := by 
      exact_mod_cast hn7
    have h9 : x = (17 : ℝ) / 13 := by 
      nlinarith [h1, h8]
    right
    linarith