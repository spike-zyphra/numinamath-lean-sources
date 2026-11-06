import Mathlib

theorem inequalities_4417 : {x : ℤ | x ^ 2 - 5 * abs x + 6 < 0} = ∅ := by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h 
  by_cases h5 : x ≥ 0 
  · -- Case x ≥ 0 
    have h6 : abs x = x := abs_of_nonneg h5
    rw [h6] at h 
    have h7 : x ^ 2 -5 * x +6 ≥ 0 := by 
      by_cases h2' : x ≤ 2 
      · -- x ≤ 2 
        have h2a' : x ≤ 2 := h2'
        have h2b' : x ≥ 0 := by linarith 
        interval_cases x <;> omega 
      · -- x > 2 
        have h2c' : x ≥ 3 := by omega 
        nlinarith [sq_nonneg ((x - 2 : ℤ)), sq_nonneg ((x - 3 : ℤ)), sq_nonneg ((x : ℤ)), sq_nonneg ((x - 5 : ℤ)), show (x - 2 : ℤ) ≥ 1 from by nlinarith, show (x - 3 : ℤ) ≥ 0 from by nlinarith] 
    linarith 
  · -- Case x < 0 
    have h7 : abs x = -x := abs_of_neg (show x < 0 by omega)
    rw [h7] at h 
    have h8 : x ^ 2 +5 * x +6 ≥ 0 := by 
      have h9 : x < 0 := by omega 
      have h10 : x ≤ -1 := by omega 
      have h11 : (x + 2) * (x + 3) ≥ 0 := by 
        by_cases h14 : x ≤ -3 
        · -- x ≤ -3 
          have h14a : x ≤ -3 := h14 
          have h14b : x + 2 ≤ -1 := by linarith 
          have h14c : x + 3 ≤ 0 := by linarith 
          nlinarith 
        · -- ¬(x ≤ -3) 
          push_neg at h14 
          have h15a : x > -3 := by linarith 
          have h16a : x = -2 ∨ x = -1 := by 
            omega 
          rcases h16a with (h17a | h17b)
          · -- x = -2 
            rw [h17a] 
            all_goals norm_num 
          · -- x = -1 
            rw [h17b] 
            all_goals norm_num 
      nlinarith 
    linarith