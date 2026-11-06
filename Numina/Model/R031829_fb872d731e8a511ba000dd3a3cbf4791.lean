import Mathlib

theorem number_theory_166 (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (h₀ : p * q * r = 2006) (h₁ : p + q = r^2 * (p + r)) :
    q = 59 := by
  have h2 : p ∣ 2006 := by
    use q * r
    linarith
  have h3 : p = 2 ∨ p = 17 ∨ p = 59 := by
    have h4 : p ∣ 2006 := h2
    have h5 : p ≤ 2006 := by
      exact Nat.le_of_dvd (by norm_num) h4
    interval_cases p <;> norm_num at hp h4 ⊢
  rcases h3 with h3 | h3 | h3
  · -- p = 2
    rw [show p = 2 by linarith [h3]] at h₀ h₁
    have h4 : q * r = 1003 := by
      nlinarith
    have h5 : q ∣ 1003 := by
      use r
      all_goals linarith
    have h6 : q = 17 ∨ q = 59 := by
      have h7 : q ∣ 1003 := h5
      have h8 : q ≤ 1003 := by
        exact Nat.le_of_dvd (by norm_num) h7
      interval_cases q <;> norm_num at h7 hq ⊢
    rcases h6 with h6 | h6
    · -- q = 17
      have h7 : r = 59 := by
        nlinarith
      rw [show q = 17 by linarith [h6], show r = 59 by linarith [h7]] at h₁
      norm_num at h₁
    · -- q = 59
      have h7 : r = 17 := by
        nlinarith
      rw [show q = 59 by linarith [h6], show r = 17 by linarith [h7]] at h₁
      norm_num at h₁
  · -- p = 17
    rw [show p = 17 by linarith [h3]] at h₀ h₁
    have h4 : q * r = 118 := by
      nlinarith
    have h5 : q ∣ 118 := by
      use r
      all_goals linarith
    have h6 : q = 2 ∨ q = 59 := by
      have h7 : q ∣ 118 := h5
      have h8 : q ≤ 118 := by
        exact Nat.le_of_dvd (by norm_num) h7
      interval_cases q <;> norm_num at h7 hq ⊢
    rcases h6 with h6 | h6
    · -- q = 2
      have h7 : r = 59 := by
        nlinarith
      rw [show q = 2 by linarith [h6], show r = 59 by linarith [h7]] at h₁
      norm_num at h₁
    · -- q = 59
      have h7 : r = 2 := by
        nlinarith
      rw [show q = 59 by linarith [h6], show r = 2 by linarith [h7]] at h₁
      norm_num at h₁
      all_goals
        nlinarith
  · -- p = 59
    rw [show p = 59 by linarith [h3]] at h₀ h₁
    have h4 : q * r = 34 := by
      nlinarith
    have h5 : q ∣ 34 := by
      use r
      all_goals linarith
    have h6 : q = 2 ∨ q = 17 := by
      have h7 : q ∣ 34 := h5
      have h8 : q ≤ 34 := by
        exact Nat.le_of_dvd (by norm_num) h7
      interval_cases q <;> norm_num at h7 hq ⊢
    rcases h6 with h6 | h6
    · -- q = 2
      have h7 : r = 17 := by
        nlinarith
      rw [show q = 2 by linarith [h6], show r = 17 by linarith [h7]] at h₁
      norm_num at h₁
    · -- q = 17
      have h7 : r = 2 := by
        nlinarith
      rw [show q = 17 by linarith [h6], show r = 2 by linarith [h7]] at h₁
      norm_num at h₁