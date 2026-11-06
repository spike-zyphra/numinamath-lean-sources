import Mathlib

theorem algebra_3888 (a : ℝ) (ha : 2 * a - ⌊a⌋ - 2 = 3) :
    a = 5 ∨ a = 4.5 := by
  let n := ⌊a⌋
  have hn1 : (n : ℝ) ≤ a := by exact Int.floor_le a
  have hn2 : a < ((n : ℝ) + 1) := by exact Int.lt_floor_add_one a
  have ha_eq : 2 * a = (n : ℝ) + 5 := by linarith 
  have a_eq : a = ((n : ℝ) + 5) / 2 := by linarith
  have h1 : (n : ℝ) ≤ ((n : ℝ) + 5) / 2 := by 
    linarith [hn1, a_eq]
  have h2 : ((n : ℝ) + 5) / 2 < ((n : ℝ) + 1) := by
    linarith [hn2, a_eq]
  have h3 : (n : ℝ) ≤ 5 := by 
    nlinarith
  have h4 : (3 : ℝ) < (n : ℝ) := by 
    nlinarith
  have hn3 : n ≤ 5 := by
    by_contra h
    push_neg at h
    have h6 : n > 5 := by omega
    have h5 : (n : ℝ) > (5 : ℝ) := by
      have h7 : n > 5 := h6
      exact_mod_cast h7
    linarith
  have hn4 : 3 < n := by
    by_contra h
    push_neg at h
    have h7 : n ≤ 3 := by omega
    have h8 : (n : ℝ) ≤ (3 : ℝ) := by
      have h9 : n ≤ 3 := h7
      exact_mod_cast h9
    linarith
  have hn5 : n = 4 ∨ n = 5 := by omega
  rcases hn5 with (h | h)
  · -- Case n = 4
    have hn4 : (n : ℝ) = (4 : ℝ) := by exact_mod_cast h
    have ha4 : a = (9 : ℝ) / 2 := by
      rw [a_eq]
      rw [hn4]
      all_goals norm_num
    have h2 : a = 4.5 := by
      rw [ha4]
      norm_num
    right
    exact h2
  · -- Case n = 5
    have hn5 : (n : ℝ) = (5 : ℝ) := by exact_mod_cast h
    have ha5 : a = (5 : ℝ) := by
      rw [a_eq]
      rw [hn5]
      all_goals norm_num
    left
    exact ha5