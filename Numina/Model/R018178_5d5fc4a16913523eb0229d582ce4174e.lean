import Mathlib

theorem number_theory_182616 (A : ℤ) (hA : A ≠ 0) (h1 : 1047 % A = 23) (h2 : 1047 % (A + 1) = 7) :
    A = 64 := by 
  have h3 : A ≤ 1047 := by 
    by_contra h 
    push_neg at h 
    have h4 : A > 1047 := h 
    have h5 : 1047 % A = 1047 := by 
      rw [Int.emod_eq_of_lt]
      all_goals omega 
    omega 
  have h5 : A ≥ -1047 := by
    by_contra h 
    push_neg at h 
    have h7 : A ≤ -1048 := by omega 
    have h8 : A + 1 ≤ -1047 := by omega 
    -- Now we will show this leads to a contradiction 
    have h11 : (A + 1) ∣ 1040 := by
      have eq1 : 1047 % (A + 1) = 7 := h2 
      have eq2 : 1047 = (A + 1) * (1047 / (A + 1)) + (1047 % (A + 1)) := by
        rw [Int.ediv_add_emod 1047 (A + 1)]
      rw [eq1] at eq2 
      use (1047 / (A + 1))
      linarith 
    have h12 : (A + 1) ≤ -1047 := h8 
    have h19 : (A + 1) ≥ -1040 := by 
      have h20 : (A + 1) ∣ 1040 := h11 
      have h21 : (A + 1) ≤ 1040 := by 
        apply Int.le_of_dvd (by norm_num) h20 
      have h22 : (A + 1) ≥ -1040 := by 
        have h23 : (- (A + 1)) ∣ 1040 := by 
          exact Int.neg_dvd.2 h20 
        have h24 : - (A + 1) ≤ 1040 := by 
          apply Int.le_of_dvd (by norm_num) h23 
        omega 
      omega 
    omega 
  interval_cases A <;> norm_num at h1 h2 ⊢ 
  <;> omega