import Mathlib

theorem algebra_608950 :
    IsLeast {t : ℕ | ∃x y : ℕ, x + y = 24 ∧ ∃x_est y_est : ℕ, 4 / 5 * (x : ℝ) ≤ x_est ∧ x_est ≤ 6 / 5 * (x : ℝ) ∧
    4 / 5 * (y : ℝ) ≤ y_est ∧ y_est ≤ 6 / 5 * (y : ℝ) ∧ t = x_est + y_est} 20 := by
  constructor
  · -- Show that 20 is in the set
    use 10, 14
    constructor
    · norm_num
    · use 8, 12
      norm_num
  · -- Show that 20 is the smallest
    intro t h
    rcases h with ⟨x, y, h_sum, x_est, y_est, h1, h2, h3, h4, ht⟩
    have h5 : (x : ℝ) + (y : ℝ) = (24 : ℝ) := by
      exact_mod_cast h_sum
    have h6 : x_est ≥ (4 / 5 * (x : ℝ) ) := by
      have h7 : (4 / 5 * (x : ℝ)) ≤ (x_est : ℝ) := by linarith
      exact_mod_cast h7
    have h7 : x_est ≤ (6 / 5 * (x : ℝ) ) := by
      have h8 : (x_est : ℝ) ≤ (6 / 5 * (x : ℝ) ) := by linarith
      exact_mod_cast h8
    have h8 : y_est ≥ (4 / 5 * (y : ℝ) ) := by
      have h9 : (4 / 5 * (y : ℝ) ) ≤ (y_est : ℝ) := by linarith
      exact_mod_cast h9
    have h9 : y_est ≤ (6 / 5 * (y : ℝ) ) := by
      have h10 : (y_est : ℝ) ≤ (6 / 5 * (y : ℝ) ) := by linarith
      exact_mod_cast h10
    have h10 : (x_est : ℝ) + (y_est : ℝ) ≥ 19.2 := by
      have eq1 : (x : ℝ) + (y : ℝ) = (24 : ℝ) := h5
      nlinarith
    have h11 : x_est + y_est ≥ 20 := by
      by_contra h
      push_neg at h
      have h12 : x_est + y_est ≤ 19 := by omega
      have h13 : (x_est : ℝ) + (y_est : ℝ) ≤ (19 : ℝ) := by
        exact_mod_cast h12
      linarith
    have h12 : t ≥ 20 := by 
      omega
    linarith