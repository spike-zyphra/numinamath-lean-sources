import Mathlib

theorem algebra_4214 {a b c : ℤ} (h : ∀ x, (x - a) * (x - 4) - 1 = (x + b) * (x + c)) :
    a = 4 := by
  have eq1 := h 4
  have eq2 : (4 + b) * (4 + c) = -1 := by
    nlinarith
  have h1 : (4 + b) ∣ -1 := by
    use (4 + c)
    all_goals linarith
  have h2 : (4 + b) ∣ (1 : ℤ) := by 
    have : (4 + b) ∣ -1 := h1
    have : (4 + b) ∣ 1 := by
      exact Int.dvd_neg.mp this
    assumption
  have h3 : (4 + b) = 1 ∨ (4 + b) = -1 := by
    have h4 : (4 + b) ∣ 1 := h2
    have : (4 + b) ≤ 1 := by 
      exact Int.le_of_dvd (show (0 : ℤ) < (1 : ℤ) by norm_num) h4
    have : (4 + b) ≥ -1 := by
      have h5 : (- (4 + b)) ∣ 1 := by
        exact Int.neg_dvd.2 h4
      have : - (4 + b) ≤ 1 := by 
        exact Int.le_of_dvd (show (0 : ℤ) < (1 : ℤ) by norm_num) h5
      omega
    interval_cases (4 + b) <;> try tauto
  rcases h3 with (h4 | h4)
  · -- Assume 4 + b = 1, so b = -3
    have hb : b = -3 := by
      linarith
    -- Then (4 + c) = -1, so c = -5
    have hc1 : (4 + c) = -1 := by
      have : (4 + b) * (4 + c) = -1 := eq2
      rw [show 4 + b = 1 by linarith] at this
      linarith
    have hc : c = -5 := by
      linarith
    -- Evaluate at x = 0
    have h0 := h 0
    rw [hb, hc] at h0
    nlinarith
  · -- Assume 4 + b = -1, so b = -5
    have hb : b = -5 := by
      linarith
    -- Then (4 + c) = 1, so c = -3
    have hc1 : (4 + c) = 1 := by
      have : (4 + b) * (4 + c) = -1 := eq2
      rw [show 4 + b = -1 by linarith] at this
      linarith
    have hc : c = -3 := by
      linarith
    -- Evaluate at x = 0
    have h0 := h 0
    rw [hb, hc] at h0
    nlinarith