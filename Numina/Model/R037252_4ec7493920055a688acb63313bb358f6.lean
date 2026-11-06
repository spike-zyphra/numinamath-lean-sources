import Mathlib

theorem algebra_2902 {x : ℝ} (hx : 4 * x - 7 * ⌊x⌋ = 13) : x = -3 - 3 / 4 := by
  let n := ⌊x⌋
  have hn1 : (n : ℝ) ≤ x := by exact Int.floor_le x
  have hn2 : x < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
  have h_eq : 4 * x = 13 + 7 * (n : ℝ) := by
    have h : (4 * x - 7 * (n : ℝ) = (13 : ℝ)) := by
      exact_mod_cast hx
    linarith
  have h4 : x = (13 + 7 * (n : ℝ) ) / 4 := by
    linarith
  have h5 : (n : ℝ) ≤ (13 + 7 * (n : ℝ) ) / 4 := by
    nlinarith [hn1, h4]
  have h6 : (13 + 7 * (n : ℝ) ) / 4 < (n + 1 : ℝ) := by
    nlinarith [h4, hn2]
  have h7 : n ≥ -4 := by
    by_contra h
    push_neg at h
    have h8 : n ≤ -5 := by omega
    have h9 : (n : ℝ) ≤ (-5 : ℝ) := by
      exact_mod_cast h8
    nlinarith
  have h8 : n ≤ -4 := by
    by_contra h
    push_neg at h
    have h9 : n ≥ -3 := by omega
    have h10 : (n : ℝ) ≥ (-3 : ℝ) := by
      exact_mod_cast h9
    nlinarith
  have hn3 : n = -4 := by
    omega
  have h10 : (n : ℝ) = (-4 : ℝ) := by
    exact_mod_cast hn3
  have hx2 : x = (-15 / 4 : ℝ) := by
    rw [h10] at h_eq
    linarith
  norm_num at hx2 ⊢
  linarith