import Mathlib

theorem algebra_260920 {x : ℝ} (hx : 4 * x - 2 * ⌊x⌋ = 5) :
    x = 1.75 ∨ x = 2.25 := by 
  let n := ⌊x⌋
  have hn1 : n ≤ (x : ℝ) := by exact Int.floor_le x
  have hn2 : (x : ℝ) < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
  have eq1 : (4 * x - 2 * (n : ℝ) = 5) := by 
    simpa [n] using hx
  have eq2 : x = (5 + 2 * (n : ℝ)) / 4 := by
    linarith 
  have h3 : (n : ℝ) ≤ (5 + 2 * (n : ℝ)) / 4 := by 
    have h1 : (n : ℝ) ≤ x := by exact Int.floor_le x
    rw [eq2] at *
    linarith 
  have h4 : (5 + 2 * (n : ℝ)) / 4 < (n + 1 : ℝ) := by 
    have h2 : x < ((n + 1) : ℝ) := by exact Int.lt_floor_add_one x
    rw [eq2] at *
    linarith 
  have h5 : n ≤ 2 := by 
    by_contra h
    push_neg at h
    have hn7 : n ≥ 3 := by omega 
    have hn8 : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast hn7
    nlinarith 
  have h6 : n ≥ 1 := by 
    by_contra h
    push_neg at h
    have h7 : n ≤ 0 := by omega 
    have hn8 : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h7
    nlinarith 
  have h7 : n = 1 ∨ n = 2 := by omega 
  rcases h7 with (h | h)
  · -- Case n = 1
    have hn1 : (n : ℝ) = 1 := by exact_mod_cast h
    have hx1 : x = 1.75 := by 
      rw [eq2]
      rw [hn1]
      norm_num 
    left 
    exact hx1 
  · -- Case n = 2
    have hn2 : (n : ℝ) = 2 := by exact_mod_cast h
    have hx2 : x = 2.25 := by 
      rw [eq2]
      rw [hn2]
      norm_num 
    right 
    exact hx2