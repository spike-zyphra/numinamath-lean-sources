import Mathlib

theorem number_theory_249749 (n : ℕ) (h : n ≠ 0) (h1 : (n + 1) * (n - 1) = 2008) :
    n = 24 := by 
  have h2 : n ≤ 45 := by 
    by_contra h2
    push_neg at h2 
    have h3 : n ≥ 46 := by omega 
    have h4 : n ≥ 46 := h3 
    have h5 : n + 1 ≥ 47 := by omega 
    have h6 : n - 1 ≥ 45 := by 
      by_cases h1' : n ≥ 46 
      · 
        omega 
      all_goals 
        omega 
    have h7 : (n + 1) * (n - 1) ≥ 47 * 45 := by 
      nlinarith 
    norm_num at h7 
    nlinarith 
    all_goals 
      omega 
  interval_cases n <;> omega 
  all_goals 
    omega