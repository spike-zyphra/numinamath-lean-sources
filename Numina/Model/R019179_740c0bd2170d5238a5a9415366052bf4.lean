import Mathlib

theorem algebra_324719 (n : ℤ) (hn : n > 0) :
    (2 / (n : ℚ) + 3 / ((n + 1) : ℚ) + 4 / ((n + 2) : ℚ)) = 133 / 60 ↔ n = 3 := by
  constructor
  · -- Assume (2 / (n : ℚ) + 3 / ((n + 1) : ℚ) + 4 / ((n + 2) : ℚ)) = 133 / 60, prove n = 3
    intro h
    have eq2 : (n : ℚ) * ((n + 1 : ℚ)) * ((n + 2 : ℚ)) ≠ 0 := by
      have h4 : (n : ℚ) ≠ 0 := by
        have h5 : n ≠ 0 := by omega
        exact_mod_cast h5
      have h5 : (n + 1 : ℚ) ≠ 0 := by
        have h6 : n + 1 ≠ 0 := by omega
        exact_mod_cast h6
      have h6 : (n + 2 : ℚ) ≠ 0 := by
        have h7 : n + 2 ≠ 0 := by omega 
        exact_mod_cast h7
      exact mul_ne_zero (mul_ne_zero h4 h5) h6
    have eq3 : ((2 / (n : ℚ) + 3 / ((n + 1) : ℚ) + 4 / ((n + 2) : ℚ)) = 133 / 60) := h 
    have eq4 : ((n : ℚ) * ((n + 1 : ℚ)) * ((n + 2 : ℚ))) * (2 / (n : ℚ) + 3 / ((n + 1 : ℚ)) + 4 / ((n + 2) : ℚ)) = 133 / 60 * ((n : ℚ) * ((n + 1 : ℚ)) * ((n + 2 : ℚ))) := by 
      rw [eq3] 
      ring_nf 
    have eq5 : ((n : ℚ) * ((n + 1 : ℚ)) * ((n + 2 : ℚ))) * (2 / (n : ℚ) + 3 / ((n + 1 : ℚ)) + 4 / ((n + 2) : ℚ)) = 2 * ((n + 1 : ℚ)) * ((n + 2 : ℚ)) + 3 * ((n : ℚ)) * ((n + 2 : ℚ)) + 4 * ((n : ℚ)) * ((n + 1 : ℚ)) := by
      field_simp [(show (n : ℚ) ≠ 0 by 
        have h5 : n ≠ 0 := by omega 
        exact_mod_cast h5 
      ), (show (n + 1 : ℚ) ≠ 0 by
        have h6 : n + 1 ≠ 0 := by omega 
        exact_mod_cast h6 
      ), (show (n + 2 : ℚ) ≠ 0 by 
        have h7 : n + 2 ≠ 0 := by omega 
        exact_mod_cast h7 
      )] 
      ring_nf 
    have eq7 : 2 * ((n + 1 : ℚ)) * ((n + 2 : ℚ)) + 3 * ((n : ℚ)) * ((n + 2 : ℚ)) + 4 * ((n : ℚ)) * ((n + 1 : ℚ)) = 133 / 60 * ((n : ℚ) * ((n + 1 : ℚ)) * ((n + 2 : ℚ))) := by 
      linarith [eq4, eq5]
    have eq8 : 120 * ((n + 1 : ℚ)) * ((n + 2 : ℚ)) + 180 * ((n : ℚ)) * ((n + 2 : ℚ)) + 240 * ((n : ℚ)) * ((n + 1 : ℚ)) = 133 * ((n : ℚ) * ((n + 1 : ℚ) ) * ((n + 2 : ℚ)) ) := by 
      have eq9 : 2 * ((n + 1 : ℚ)) * ((n + 2 : ℚ)) + 3 * ((n : ℚ)) * ((n + 2 : ℚ)) + 4 * ((n : ℚ)) * ((n + 1 : ℚ)) = 133 / 60 * ((n : ℚ) * ((n + 1 : ℚ)) * ((n + 2 : ℚ))) := eq7 
      linarith [eq9]
    have eq10 : 120 * ((n + 1 : ℤ)) * ((n + 2 : ℤ)) + 180 * ((n : ℤ)) * ((n + 2 : ℤ)) + 240 * ((n : ℤ)) * ((n + 1 : ℤ)) = 133 * ((n : ℤ) * ((n + 1 : ℤ)) * ((n + 2 : ℤ)) ) := by 
      have eq11 : (120 : ℚ) * ((n + 1 : ℚ)) * ((n + 2 : ℚ)) + (180 : ℚ) * ((n : ℚ)) * ((n + 2 : ℚ)) + (240 : ℚ) * ((n : ℚ)) * ((n + 1 : ℚ)) = (133 : ℚ) * ((n : ℚ) * ((n + 1 : ℚ)) * ((n + 2 : ℚ)) ) := by 
        linarith [eq8]
      exact_mod_cast eq11 
    have h4 : n ≤ 5 := by 
      nlinarith [sq_nonneg (n - 3 : ℤ), sq_nonneg (n - 1 : ℤ), sq_nonneg (n - 0 : ℤ), sq_nonneg (n + 1 : ℤ), sq_nonneg (n + 2 : ℤ)]
    interval_cases n <;> norm_num at eq10 ⊢ <;> tauto 
  · -- Assume n = 3, prove (2 / (n : ℚ) + 3 / ((n + 1) : ℚ) + 4 / ((n + 2) : ℚ)) = 133 / 60 
    intro h_eq 
    rw [show n = 3 by linarith]
    norm_num