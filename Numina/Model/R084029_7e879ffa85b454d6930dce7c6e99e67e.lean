import Mathlib

theorem number_theory_1515 (a b : ℤ) (h : a^2 - b^2 = 1993) : |a * b| = 993012 := by
  have h1 : a^2 - b^2 = (a - b) * (a + b) := by ring
  rw [h1] at h
  have h2 : (a - b) * (a + b) = 1993 := h
  have h3 : (a - b) ∣ 1993 := by
    use (a + b)
    linarith
  have h5 : (a - b) = 1 ∨ (a - b) = -1 ∨ (a - b) = 1993 ∨ (a - b) = -1993 := by 
    have h6 : (a - b) ∣ 1993 := h3
    have h7 : (a - b) ≤ 1993 := by 
      exact Int.le_of_dvd (by norm_num) h6
    have h8 : (a - b) ≥ -1993 := by
      have h9 : -(a - b) ∣ 1993 := by 
        exact Int.neg_dvd.2 h6
      have h10 : -(a - b) ≤ 1993 := by 
        exact Int.le_of_dvd (by norm_num) h9
      linarith
    interval_cases (a - b) <;> omega 
  rcases h5 with (h6 | h7 | h8 | h9)
  · -- Case where a - b = 1 
    have h10 : (a + b) = 1993 := by
      nlinarith 
    have ha : a = 997 := by 
      linarith 
    have hb : b = 996 := by 
      linarith 
    rw [ha, hb]
    norm_num [abs_of_nonneg]
  · -- Case where a - b = -1 
    have h11 : (a + b) = -1993 := by
      nlinarith 
    have ha : a = -997 := by 
      linarith 
    have hb : b = -996 := by 
      linarith 
    rw [ha, hb]
    norm_num [abs_of_nonneg]
  · -- Case where a - b = 1993 
    have h12 : (a + b) = 1 := by
      nlinarith 
    have ha : a = 997 := by 
      linarith 
    have hb : b = -996 := by 
      linarith 
    rw [ha, hb]
    norm_num [abs_of_nonneg]
  · -- Case where a - b = -1993 
    have h13 : (a + b) = -1 := by
      nlinarith 
    have ha : a = -997 := by 
      linarith 
    have hb : b = 996 := by 
      linarith 
    rw [ha, hb]
    norm_num [abs_of_nonneg]