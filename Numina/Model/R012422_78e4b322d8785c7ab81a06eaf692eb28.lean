import Mathlib

theorem number_theory_2786 {n : ℕ} (hn : n ≠ 0) (b : ℕ) (hb : b > (40 / 100 : ℝ) * n ∧ b < (50 / 100 : ℝ) * n) :
    n ≥ 7 := by

  by_contra h
  push_neg at h
  
  have h1 : n < 7 := h
  have h2 : n > 0 := by
    by_contra h3
    push_neg at h3 
    have h4 : n = 0 := by 
      omega
    contradiction
  
  have hb1 := hb.left
  have hb2 := hb.right
  
  have h3 : (b : ℝ) > (40 / 100 : ℝ) * (n : ℝ) := by
    simpa using hb1
  
  have h4 : (b : ℝ) < (50 / 100 : ℝ) * (n : ℝ) := by
    simpa using hb2
  
  have h5 : 5 * (b : ℝ) > (2 * (n : ℝ) : ℝ) := by 
    nlinarith
  
  have h6 : 2 * (b : ℝ) < (n : ℝ) := by 
    nlinarith
  
  have h7 : 5 * b > 2 * n := by
    exact_mod_cast h5
  
  have h8 : 2 * b < n := by
    exact_mod_cast h6
  
  interval_cases n <;> omega