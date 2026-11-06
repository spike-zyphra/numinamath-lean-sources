import Mathlib

theorem algebra_3185 : IsGreatest {s : ℤ | ∃ x y : ℤ, 0 < x ∧ 0 < y ∧
    x * y - 7 * x - 3 * y + 9 = 0 ∧ s = x ^ 2 + y ^ 2} 377 := by 
  constructor 
  · -- Show 377 is in the set 
    use 4, 19 
    all_goals norm_num 
  · -- Show 377 is greatest 
    intro s hs 
    rcases hs with ⟨x, y, hx_pos, hy_pos, he, hs⟩
    have h1 : x * y - 7 * x - 3 * y + 9 = 0 := he 
    have h2 : (x - 3) * (y - 7) = 12 := by 
      nlinarith 
    have h3 : x - 3 ∣ 12 := by 
      use y - 7 
      all_goals linarith 
    have h4 : x - 3 ≤ 12 := by 
      exact Int.le_of_dvd (by norm_num) h3 
    have h5 : x - 3 ≥ -12 := by 
      have h6 : - (x - 3) ∣ 12 := by 
        exact Int.neg_dvd.2 h3 
      have h7 : - (x - 3) ≤ 12 := by 
        apply Int.le_of_dvd (by norm_num) h6 
      omega 
    interval_cases h6 : x - 3 <;> norm_num at h2 h6 
    all_goals try { 
      omega 
    }
    all_goals try { 
      have eq1 : x = 3 + (x - 3) := by omega 
      have eq2 : y = 7 + (y - 7) := by omega
      have h377 : s ≤ 377 := by 
        nlinarith [sq_nonneg (x - 4 : ℤ), sq_nonneg ((y - 19) : ℤ), sq_nonneg ((x - 15) : ℤ), sq_nonneg ((y - 8) : ℤ)]
      linarith 
    }