import Mathlib

theorem algebra_185859 (v : ℕ) (h : v ≥ 6) (h' : 11 / v + 6 / (v - 6) < 11 / (v - 6) + 6 / v) :
    v ≤ 26 := by
  by_contra h1
  push_neg at h1
  have h1' : v ≥ 27 := by linarith
  have h21 : 11 / v = 0 := by
    have h3 : v ≥ 27 := h1'
    have h4 : (11 : ℕ) / v = 0 := by
      norm_num
      all_goals omega
    linarith
  have h22 : 6 / (v - 6) = 0 := by
    have h5 : v - 6 ≥ 21 := by omega
    have h6 : (6 : ℕ) / (v - 6) = 0 := by
      norm_num
      all_goals omega
    linarith
  have h23 : 11 / (v - 6) = 0 := by
    have h5 : v - 6 ≥ 21 := by omega
    have h6 : (11 : ℕ) / (v - 6) = 0 := by
      norm_num
      all_goals omega
    linarith
  have h24 : 6 / v = 0 := by
    have h3 : v ≥ 27 := h1'
    have h4 : (6 : ℕ) / v = 0 := by
      norm_num
      all_goals omega
    linarith
  simp [h21, h22, h23, h24] at h'
  all_goals omega