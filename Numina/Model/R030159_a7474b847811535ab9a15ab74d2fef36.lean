import Mathlib

open Real

theorem algebra_12077 : IsGreatest {x : ℤ | x < ∑ i ∈ Finset.Icc (1 : ℕ) 2009, logb 2 ((i + 1) / i)} 10 := by 
  have h1 : ∑ i ∈ Finset.Icc (1 : ℕ) 2009, logb 2 ((i + 1) / i) = logb 2 (2010 : ℝ) := by 
    have h2 : ∀ (n : ℕ), ∑ i ∈ Finset.Icc (1 : ℕ) n, logb 2 ((i + 1) / i) = logb 2 ((n + 1 : ℝ)) := by 
      intro n
      induction n with
      | zero =>
        norm_num [Finset.sum_singleton, logb_div, logb_one]
      | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by linarith)]
        rw [ih]
        field_simp [logb_div, logb_one] at *
        <;> ring_nf <;> norm_num
    rw [h2 2009]
    all_goals norm_num
  constructor
  · -- Show that 10 is in the set
    have h2 : (10 : ℤ) < ∑ i ∈ Finset.Icc (1 : ℕ) 2009, logb 2 ((i + 1) / i) := by 
      have h3 : logb 2 (2010 : ℝ) > (10 : ℝ) := by 
        have h4 : logb 2 (2010 : ℝ) > logb 2 (1024 : ℝ) := by 
          apply Real.logb_lt_logb 
          all_goals norm_num 
        have h5 : logb 2 (1024 : ℝ) = 10 := by 
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
        linarith [h4, h5] 
      have h4' : (10 : ℝ) < ∑ i ∈ Finset.Icc (1 : ℕ) 2009, logb 2 ((i + 1) / i) := by 
        rw [h1] 
        linarith [h3] 
      exact_mod_cast h4' 
    exact h2
  · -- Show that 10 is greatest 
    intro x hx
    have h3' : (x : ℤ) < ∑ i ∈ Finset.Icc (1 : ℕ) 2009, logb 2 ((i + 1) / i) := by 
      have h6 : x ∈ {x : ℤ | x < ∑ i ∈ Finset.Icc (1 : ℕ) 2009, logb 2 ((i + 1) / i)} := hx 
      simpa using h6 
    have h4' : (x : ℝ) < logb 2 (2010 : ℝ) := by 
      have h5 : ∑ i ∈ Finset.Icc (1 : ℕ) 2009, logb 2 ((i + 1) / i) = logb 2 (2010 : ℝ) := h1 
      have h4 : (x : ℝ) < ( ∑ i ∈ Finset.Icc (1 : ℕ) 2009, logb 2 ((i + 1) / i) ) := by 
        exact_mod_cast h3' 
      rw [h5] at h4 
      linarith 
    have h5 : logb 2 (2010 : ℝ) < (11 : ℝ) := by 
      have h6 : logb 2 (2010 : ℝ) < logb 2 (2048 : ℝ) := by 
        apply Real.logb_lt_logb 
        all_goals norm_num 
      have h7 : logb 2 (2048 : ℝ) = 11 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num 
      linarith 
    have h6' : (x : ℝ) < (11 : ℝ) := by 
      linarith [h4', h5] 
    have h7' : x ≤ 10 := by 
      by_contra h 
      push_neg at h 
      have h8' : x ≥ 11 := by 
        omega 
      have h8 : (x : ℝ) ≥ (11 : ℝ) := by 
        exact_mod_cast h8' 
      linarith [h6', h8] 
    linarith