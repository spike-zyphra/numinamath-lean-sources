import Mathlib

theorem algebra_283455 {a b c : ℤ} (ha : a ≠ 10) (h : ∀ x, (x - a) * (x - 10) + 1 = (x + b) * (x + c)) :
    a = 8 ∨ a = 12 := by

  have eq1 := h 10
  have eq1_simp : (10 + b) * (10 + c) = 1 := by
    nlinarith
  
  have h1 : (10 + b) * (10 + c) = 1 := eq1_simp
  
  have h2 : 10 + b = 1 ∨ 10 + b = -1 := by
    have h3 : (10 + b) * (10 + c) = 1 := h1
    have h5 : (10 + b) ∣ 1 := by
      use (10 + c)
      all_goals linarith
    have : (10 + b) = 1 ∨ (10 + b) = -1 := by
      have : (10 + b) ∣ 1 := h5
      have h7 : (10 + b) ≤ 1 := by
        apply Int.le_of_dvd (by norm_num) this
      have h8 : (10 + b) ≥ -1 := by
        have : (- (10 + b)) ∣ 1 := by
          exact Int.neg_dvd.2 this
        have h5 : - (10 + b) ≤ 1 := by
          apply Int.le_of_dvd (by norm_num) this
        omega
      interval_cases (10 + b) <;> tauto
    assumption
  
  rcases h2 with h2 | h2
  
  · -- 10 + b = 1
    have hb : b = -9 := by
      omega
  
    have hc : c = -9 := by
      rw [hb] at h1
      nlinarith
  
    have eq2 := h 0
    simp [hb, hc] at eq2
    have h3 : a = 8 := by
      nlinarith
  
    left
    assumption
  
  · -- 10 + b = -1
    have hb : b = -11 := by
      omega
  
    have hc : c = -11 := by
      rw [hb] at h1
      nlinarith
  
    have eq2 := h 0
    simp [hb, hc] at eq2
    have h3 : a = 12 := by
      nlinarith
  
    right
    assumption