import Mathlib

theorem algebra_184226 {x y : ℤ} (h : x^2 = (y + 1)^2 + 1) (h' : x^2 - (y + 1)^2 = 1)
    (h'' : (x - y - 1) * (x + y + 1) = 1) :
    (x = 1 ∧ y = -1) ∨ (x = -1 ∧ y = -1) := by
  have h_eq1 : (x - y - 1) = 1 ∨ (x - y - 1) = -1 := by
    have h3 : (x - y - 1) * (x + y + 1) = 1 := h''
    have h4 : (x - y - 1) ∣ 1 := by 
      use (x + y + 1)
      linarith
    have h5 : (x - y - 1) = 1 ∨ (x - y - 1) = -1 := by
      have h6 : (x - y - 1) ≤ 1 := by 
        apply Int.le_of_dvd (by norm_num) h4
      have h7 : (x - y - 1) ≥ -1 := by
        have h8 : (- (x - y - 1) : ℤ) ∣ 1 := by 
          exact Int.neg_dvd.2 h4
        have h9 : (- (x - y - 1) : ℤ) ≤ 1 := by 
          apply Int.le_of_dvd (by norm_num) h8
        have h10 : (- (x - y - 1) : ℤ) ≥ -1 := by 
          omega
        have h11 : (x - y - 1) ≥ -1 := by 
          linarith
        linarith
      interval_cases (x - y - 1) <;> tauto
    exact h5
  cases h_eq1 with
  | inl h1 =>
    have h2 : (x + y + 1) = 1 := by 
      rw [h1] at h''
      nlinarith
    have hx1 : x = 1 := by
      linarith [h1, h2]
    have hy1 : y = -1 := by
      linarith [h1, h2]
    left
    exact ⟨hx1, hy1⟩
  | inr h2 =>
    have h1 : (x + y + 1) = -1 := by 
      rw [h2] at h''
      nlinarith
    have hx1 : x = -1 := by
      linarith [h1, h2]
    have hy1 : y = -1 := by
      linarith [h1, h2]
    right
    exact ⟨hx1, hy1⟩