import Mathlib

theorem algebra_163538 {a b : ℕ} (h₀ : a / b = 36) (h₁ : (a / 7) * 36 = 756) :
    a / b = 972 / 27 := by 
  have h2 : a / 7 = 21 := by
    omega
  have h3 : b ≤ 4 := by
    by_contra h
    push_neg at h
    have h4 : a ≥ 36 * b := by
      by_cases h5 : b = 0
      · 
        rw [h5] at h₀
        norm_num at h₀
      · 
        have : a = b * (a / b) + a % b := by 
          rw [Nat.div_add_mod a b]
        rw [show a / b = 36 by omega] at this
        have h5 : a % b < b := by 
          apply Nat.mod_lt
          omega
        have h5' : b ≥ 1 := by 
          by_contra h
          push_neg at h
          have : b = 0 := by linarith
          tauto
        omega
    have h5 : b ≥ 5 := by 
      omega
    have h6 : a < 154 := by
      omega
    nlinarith
  have h4 : b ≥ 4 := by
    by_contra h
    push_neg at h
    have h4 : b ≤ 3 := by 
      omega
    interval_cases b <;> 
      try { 
        omega 
      } 
    <;> try { 
      omega 
    }
  have h5 : b = 4 := by 
    omega
  have h6 : a / 4 = 36 := by 
    rw [show b = 4 by omega] at h₀
    all_goals 
      omega
  have ha : a = 147 := by
    have h7 : a / 7 = 21 := h2
    have h8 : a / 4 = 36 := h6
    omega
  calc 
    a / b = 147 / 4 := by 
      rw [show a = 147 by omega, show b = 4 by omega]
    _ = 36 := by 
      norm_num
    _ = 972 / 27 := by 
      norm_num