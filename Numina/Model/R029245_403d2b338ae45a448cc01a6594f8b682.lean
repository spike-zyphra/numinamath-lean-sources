import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_319497 {x : ℝ} (hx : 0 < x) :
    abs (1 / (logb (1 / 3) x + 1)) > 1 / 3 ↔
    (1 / 9 < x ∧ x < 3 ∨ 3 < x ∧ x < 81) := by
  have h1 : logb (1 / 3) x = -logb 3 x := by
    rw [logb]
    simp [logb]
    all_goals linarith
  rw [h1]
  constructor
  · -- First direction: abs (1 / (-logb 3 x + 1)) > 1 / 3 → (1 / 9 < x ∧ x < 3 ∨ 3 < x ∧ x < 81)
    intro h
    have h2 : -logb 3 x + 1 ≠ 0 := by
      by_contra h3
      have h4 : logb 3 x = 1 := by linarith
      have h5 : x = 3 := by
        rw [logb_eq_iff_rpow_eq] at h4
        · linarith
        all_goals linarith
      rw [h5] at h
      norm_num [logb] at h
    have h4 : abs (-logb 3 x + 1) < 3 := by
      by_contra h5
      have h7 : abs (1 / (-logb 3 x + 1)) ≤ 1 / 3 := by
        have h8 : abs (1 / (-logb 3 x + 1)) = 1 / abs (-logb 3 x + 1) := by
          field_simp [abs_div, h2]
        rw [h8]
        have h10 : (1 : ℝ) / abs (-logb 3 x + 1) ≤ 1 / 3 := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith
        linarith
      linarith
    have h5 : -2 < logb 3 x := by
      cases' abs_cases (-logb 3 x + 1) with h6 h6
      · 
        linarith
      · 
        linarith
    have h6 : logb 3 x < 4 := by
      cases' abs_cases (-logb 3 x + 1) with h7 h7
      · 
        linarith
      · 
        linarith
    have h7 : 1 / 9 < x := by
      have h8 : logb 3 x > -2 := by linarith
      have h9 : logb 3 (1 / 9 : ℝ) = -2 := by
        rw [show (1 / 9 : ℝ) = (3 ^ (-2 : ℝ)) by norm_num]
        simp [logb_rpow]
      have h10 : x > (1 / 9 : ℝ) := by
        have h11 : logb 3 x > logb 3 (1 / 9 : ℝ) := by linarith [h8, h9]
        have h13 : x > (1 / 9 : ℝ) := by
          apply (Real.logb_lt_logb_iff (by linarith) (by linarith) (by linarith)).mp h11
        linarith
      linarith
    have h8 : x < (81 : ℝ) := by
      have h9 : logb 3 x < (4 : ℝ) := by linarith
      have h10 : logb 3 (81 : ℝ) = (4 : ℝ) := by
        rw [show (81 : ℝ) = (3 ^ (4 : ℝ)) by norm_num]
        simp [logb_rpow]
      have h11 : x < (81 : ℝ) := by
        have h12 : logb 3 x < logb 3 (81 : ℝ) := by linarith [h9, h10]
        have h13 : x < (81 : ℝ) := by
          apply (Real.logb_lt_logb_iff (by linarith) (by linarith) (by linarith)).mp h12
        linarith
      linarith
    have h9 : x ≠ 3 := by
      by_contra h10
      have h11 : -logb 3 x + 1 = 0 := by
        rw [h10]
        norm_num [logb]
      contradiction
    by_cases h10 : x < 3
    · 
      left
      constructor
      · linarith
      · 
        linarith
    · 
      have h11 : x > 3 := by
        by_contra h12
        push_neg at h12
        have h14 : x = 3 := by
          linarith
        contradiction
      right
      constructor
      · linarith
      · 
        linarith
  · -- Second direction: (1 / 9 < x ∧ x < 3 ∨ 3 < x ∧ x < 81) → abs (1 / (-logb 3 x + 1)) > 1 / 3
    intro h
    rcases h with (h | h)
    · -- Case 1: 1/9 < x ∧ x < 3
      have h7 : 1 / 9 < x := h.1
      have h8 : x < 3 := h.2
      have h9 : logb 3 x > -2 := by
        have h10 : logb 3 x > logb 3 (1 / 9 : ℝ) := by
          apply Real.logb_lt_logb 
          all_goals nlinarith
        have h11 : logb 3 (1 / 9 : ℝ) = -2 := by
          rw [show (1 / 9 : ℝ) = (3 ^ (-2 : ℝ)) by norm_num]
          simp [logb_rpow]
        linarith
      have h10 : logb 3 x < 1 := by
        have h11 : logb 3 x < logb 3 (3 : ℝ) := by
          apply Real.logb_lt_logb
          all_goals nlinarith
        have h12 : logb 3 (3 : ℝ) = 1 := by
          rw [logb_eq_iff_rpow_eq] <;> norm_num 
        linarith
      have h11 : -logb 3 x + 1 > 0 := by 
        nlinarith
      have h6 : abs (1 / (-logb 3 x + 1)) > 1 / 3 := by
        have h8 : abs (1 / (-logb 3 x + 1)) = 1 / (-logb 3 x + 1) := by
          rw [abs_of_pos]
          positivity
        rw [h8]
        have h14 : -logb 3 x + 1 > 0 := by
          nlinarith
        have h15 : (-logb 3 x + 1) < 3 := by
          nlinarith
        apply (lt_div_iff' (by positivity)).mpr
        nlinarith
      linarith
    · -- Case 2: 3 < x ∧ x < 81
      have h7 : 3 < x := h.1
      have h8 : x < 81 := h.2
      have h9 : logb 3 x > 1 := by
        have h10 : logb 3 x > logb 3 (3 : ℝ) := by
          apply Real.logb_lt_logb
          all_goals nlinarith
        have h11 : logb 3 (3 : ℝ) = 1 := by
          rw [logb_eq_iff_rpow_eq] <;> norm_num 
        linarith
      have h10 : logb 3 x < 4 := by
        have h11 : logb 3 x < logb 3 (81 : ℝ) := by
          apply Real.logb_lt_logb 
          all_goals nlinarith
        have h12 : logb 3 (81 : ℝ) = 4 := by
          rw [show (81 : ℝ) = (3 ^ (4 : ℝ)) by norm_num]
          simp [logb_rpow]
        linarith
      have h11 : -logb 3 x + 1 < 0 := by 
        nlinarith
      have h6 : abs (1 / (-logb 3 x + 1)) > 1 / 3 := by
        have h17 : abs (1 / (-logb 3 x + 1)) = abs (1 / (-logb 3 x + 1) ) := by 
          rfl
        have h17a : abs (1 / (-logb 3 x + 1) ) = 1 / abs (-logb 3 x + 1) := by
          field_simp [abs_div]
          all_goals try linarith
        rw [h17, h17a]
        have h18a : abs (-logb 3 x + 1) = (-logb 3 x + 1) * (-1) := by
          have h9' : (-logb 3 x + 1) < 0 := h11
          have h10' : abs (-logb 3 x + 1) = (-logb 3 x + 1) * (-1) := by
            rw [abs_of_neg h9']
            all_goals ring
          linarith [h10']
        have h19a : abs (-logb 3 x + 1) = logb 3 x - 1 := by
          linarith [h18a]
        rw [h19a]
        have h20a : (logb 3 x - 1 : ℝ) > 0 := by
          nlinarith
        have h21a : 1 / (logb 3 x - 1 : ℝ) > 1 / 3 := by
          apply (one_div_lt_one_div (by linarith) (by linarith)).mpr
          nlinarith
        linarith [h21a]
      linarith