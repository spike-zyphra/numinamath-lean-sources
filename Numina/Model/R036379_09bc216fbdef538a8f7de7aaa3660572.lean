import Mathlib

theorem algebra_11105 (a b : ℤ) (ha : a < Real.logb 10 17) (hb : Real.logb 10 17 < b)
    (h : ∃ n, a = n ∧ b = n + 1) : a + b = 3 := by
  rcases h with ⟨n, ha_eq, hb_eq⟩
  have h1 : (n : ℝ) < Real.logb 10 17 := by
    rw [ha_eq] at ha
    exact_mod_cast ha
  have h2 : Real.logb 10 17 < (n + 1 : ℝ) := by
    rw [hb_eq] at hb
    exact_mod_cast hb
  have h3 : 1 < Real.logb 10 17 := by
    have h4 : Real.logb 10 17 > Real.logb 10 10 := by
      apply Real.logb_lt_logb
      all_goals norm_num
    have h5 : Real.logb 10 10 = 1 := Real.logb_self_eq_one (by norm_num)
    linarith
  have h4 : Real.logb 10 17 < 2 := by
    have h7 : Real.logb 10 17 < Real.logb 10 100 := by
      apply Real.logb_lt_logb
      all_goals norm_num
    have h8 : Real.logb 10 100 = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)
    linarith
  have hn1 : n ≥ 1 := by
    by_contra h
    push_neg at h
    have h2' : n ≤ 0 := by omega
    have h8 : (n : ℝ) ≤ (0 : ℝ) := by
      exact_mod_cast h2'
    have h9 : (n + 1 : ℝ) ≤ (1 : ℝ) := by
      nlinarith
    linarith [h2, h9, h3]
  have hn2 : n ≤ 1 := by
    by_contra h
    push_neg at h
    have h14 : n ≥ 2 := by omega
    have h12 : (n : ℝ) ≥ (2 : ℝ) := by
      exact_mod_cast h14
    linarith [h1, h4, Real.logb_pos (by norm_num : (10 : ℝ) > 1) (by norm_num : (17 : ℝ) > 1)]
  have hn_eq : n = 1 := by omega
  rw [ha_eq, hb_eq, hn_eq]
  norm_num