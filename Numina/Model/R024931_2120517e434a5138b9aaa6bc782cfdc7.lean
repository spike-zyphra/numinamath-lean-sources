import Mathlib

theorem algebra_164087 {x : ℝ} (h : 3 * x + 5 * ⌊x⌋ - 2017 = 0) :
    x = 252 + 1 / 3 := by
  let n := ⌊x⌋
  have hn1 : (n : ℝ) ≤ x := by exact Int.floor_le x
  have hn2 : x < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
  have eq1 : 3 * x + 5 * (n : ℝ) = 2017 := by
    have h' : (⌊x⌋ : ℝ) = (n : ℝ) := by simp
    rw [show (⌊x⌋ : ℝ) = (n : ℝ) by simp] at h
    linarith
  have eq2 : 3 * x = 2017 - 5 * (n : ℝ) := by
    linarith [eq1]

  have eq5 : 8 * (n : ℝ) ≤ 2017 := by
    nlinarith [eq2, hn1]
  have eq6 : 2014 < 8 * (n : ℝ) := by
    nlinarith [eq2, hn2]

  have hn3 : n = 252 := by
    have h7 : n ≤ 252 := by
      by_contra h8
      push_neg at h8
      have h8' : n ≥ 253 := by omega
      have h8'' : (n : ℝ) ≥ (253 : ℝ) := by exact_mod_cast h8'
      nlinarith [eq5, h8'']
    have h8 : n > 251 := by
      by_contra h9
      push_neg at h9
      have h9' : n ≤ 251 := by omega
      have h9'' : (n : ℝ) ≤ (251 : ℝ) := by exact_mod_cast h9'
      nlinarith [eq6, h9'']
    have h9 : n = 252 := by omega
    exact h9

  have eq7 : (n : ℝ) = (252 : ℝ) := by
    exact_mod_cast hn3

  have eq8 : x = (757 / 3 : ℝ) := by
    rw [eq7] at eq1
    linarith 
  rw [eq8]
  norm_num