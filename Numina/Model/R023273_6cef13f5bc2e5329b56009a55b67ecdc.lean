import Mathlib

theorem algebra_237987 {a b : ℕ} (h₀ : a * b = 2250) (h₁ : (a - 6) * b = 1800) :
    a = 30 ∧ b = 75 := by 
  have h5 : a ≥ 6 := by 
    by_contra h 
    push_neg at h 
    have h6 : a < 6 := by linarith 
    interval_cases a <;> omega 
  have h6 : a * b = 2250 := h₀
  have h7 : a * b = 2250 := h₀ 
  have h8 : a * b = 6 * b + 1800 := by 
    have h9 : a ≥ 6 := h5 
    have h10 : (a - 6) * b = 1800 := h₁ 
    have h11 : a * b = (a - 6) * b + 6 * b := by 
      have : a ≥ 6 := h9 
      cases a with 
      | zero => 
        omega -- contradiction 
      | succ a => 
        cases a with 
        | zero => 
          omega -- contradiction 
        | succ a => 
          cases a with 
          | zero => 
            omega -- contradiction 
          | succ a => 
            cases a with 
            | zero => 
              omega -- contradiction 
            | succ a => 
              simp [Nat.sub_mul, Nat.mul_sub, Nat.sub_zero, Nat.add_assoc, Nat.mul_add, Nat.add_mul] at *
              all_goals 
                ring_nf at * 
                <;> omega 
    linarith [h10, h11] 
  have hb : b = 75 := by
    nlinarith [h₀, h8]
  have ha : a = 30 := by
    rw [hb] at h₀
    nlinarith 
  exact ⟨ha, hb⟩