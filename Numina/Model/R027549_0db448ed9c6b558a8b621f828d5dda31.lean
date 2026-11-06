import Mathlib

theorem number_theory_5144 :
    IsLeast {x : ℚ | ∃ m n : ℤ, m > -8 ∧ n > -8 ∧ m < 7 ∧ n < m ∧ x = m / n ^ 2} (-1 / 4) := by
  constructor
  · -- Show that -1/4 is in the set
    use -1, -2
    norm_num
  · -- Show that -1/4 is the minimum element in the set
    intro x hx
    rcases hx with ⟨m, n, hm1, hn1, hm2, hnm, hx⟩
    by_contra h
    push_neg at h 
    have h1 : (m : ℚ) / (n ^ 2 : ℚ) < -1 / 4 := by 
      linarith [hx, h]
    have h2 : (m : ℚ) / (n ^ 2 : ℚ) < -1 / 4 := h1 
    have h3 : n ≠ 0 := by 
      by_contra h_eq 
      rw [h_eq] at h1 
      norm_num at h1 
    have h4 : (4 * (m : ℚ) + (n ^ 2 : ℚ)) < 0 := by 
      have h4 : (n : ℚ) ≠ 0 := by 
        exact_mod_cast h3 
      have h5 : (n ^ 2 : ℚ) > 0 := by 
        have hn0 : (n : ℚ) ≠ 0 := h4 
        have hn2 : (n ^ 2 : ℚ) > 0 := by 
          exact sq_pos_of_ne_zero hn0 
        linarith 
      have h6 : (m : ℚ) / (n ^ 2 : ℚ) < -1 / 4 := h1 
      have h9 : (4 * (m : ℚ) + (n ^ 2 : ℚ)) < 0 := by 
        by_contra h
        push_neg at h 
        have : (m : ℚ) / (n ^ 2 : ℚ) ≥ -1 / 4 := by 
          have h8 : (4 * (m : ℚ) + (n ^ 2 : ℚ)) ≥ 0 := by linarith 
          have h15 : (n ^ 2 : ℚ) > 0 := h5 
          have h9 : (m / (n ^ 2 : ℚ) ) ≥ -1 / 4 := by 
            apply (le_div_iff₀ (by linarith)).mpr 
            nlinarith 
          linarith 
        linarith 
      linarith 
    have h5 : (4 * m + n ^ 2 : ℤ) < 0 := by 
      exact_mod_cast h4 
    have h6 : n ≥ -7 := by omega 
    have h7 : n ≤ 6 := by omega 
    have h8 : m ≤ 6 := by omega 
    have h9 : m ≥ -7 := by omega 
    interval_cases n <;> interval_cases m 
    <;> norm_num at h5 <;> omega