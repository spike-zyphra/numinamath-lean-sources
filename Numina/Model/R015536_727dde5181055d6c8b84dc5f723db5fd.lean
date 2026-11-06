import Mathlib

theorem number_theory_37997 (n : ℕ) (hn : n ≠ 0) (h1 : (1 / 3 : ℚ) < (n * (1 - 3 / 10 : ℚ))) (h2 : (n * (1 - 3 / 10 : ℚ)) < (n * (1 - 4 / 11 : ℚ))) :
    n ≥ 173 := by
  have h3 : (n : ℚ) > (0 : ℚ) := by
    have hne : (n : ℚ) ≠ 0 := by
      exact_mod_cast show (n : ℕ) ≠ 0 by 
        omega
    have h4 : (n : ℚ) > (0 : ℚ) := by
      by_contra h
      push_neg at h
      have hness : (n : ℚ) = 0 := by linarith
      contradiction
    exact_mod_cast h4
  have h4_rat : (1 - 3 / 10 : ℚ) = (7 / 10 : ℚ) := by norm_num -- Renamed h4 to avoid collision
  have h5 : (1 - 4 / 11 : ℚ) = (7 / 11 : ℚ) := by norm_num
  rw [h4_rat] at h1 h2 
  rw [h5] at h2
  have h6 : (n : ℚ) * (7 / 10 : ℚ) < (n : ℚ) * (7 / 11 : ℚ) := by linarith
  have h4 : (n : ℚ) * (7 / 10 : ℚ) - (n : ℚ) * (7 / 11 : ℚ) < (0 : ℚ) := by 
    linarith
  have h5' : (n : ℚ) * (7 / 10 : ℚ) - (n : ℚ) * (7 / 11 : ℚ) = (7 * (n : ℚ) ) / (110 : ℚ) := by 
    field_simp
    <;> ring
  rw [h5'] at h4
  -- h4 is (7n)/110 < 0. This is a contradiction as n > 0.
  have h8 : (7 * (n : ℚ) ) < (0 : ℚ) := by
    have h11 : (7 * (n : ℚ) ) / (110 : ℚ) < (0 : ℚ) := by 
      linarith
    have h12 : (7 * (n : ℚ) ) < (0 : ℚ) := by
      have h11' : (0 : ℚ) < (110 : ℚ) := by norm_num
      have h14 : (7 * (n : ℚ) ) < (0 : ℚ) := by
        by_contra h
        push_neg at h
        have h15 : (7 * (n : ℚ) ) / (110 : ℚ) ≥ (0 : ℚ) := by
          apply div_nonneg
          linarith
          linarith
        linarith
      linarith
    linarith
  have h8' : (n : ℚ) < (0 : ℚ) := by
    nlinarith
  -- Contradiction
  have h9' : (n : ℚ) > (0 : ℚ) := by
    exact_mod_cast show (0 : ℕ) < n by
      omega
  linarith