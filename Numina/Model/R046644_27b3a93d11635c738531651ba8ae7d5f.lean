import Mathlib

theorem algebra_266709 {a b : ℕ} (ha : a = 152) (hb : b ≠ 0) (h : 125 / b = a / b - 3 ∧ 125 % b = a % b) :
    a % b = 8 := by
  rw [ha] at h
  rcases h with ⟨h1, h2⟩
  have h3 : b ≤ 152 := by
    by_contra h4
    push_neg at h4
    have h5 : 152 / b = 0 := by
      have h6 : b > 152 := h4
      have h7 : 152 / b = 0 := by
        rw [Nat.div_eq_zero_iff]
        omega
      assumption
    have h8 : 125 / b = 0 := by
      have h9 : b > 125 := by
        omega
      have h10 : 125 / b = 0 := by
        rw [Nat.div_eq_zero_iff]
        omega
      assumption
    have h7 : 125 % b = 125 := by
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    have h8 : 152 % b = 152 := by
      rw [Nat.mod_eq_of_lt]
      all_goals omega
    omega
  have h4 : b ≤ 152 := h3
  interval_cases b <;> norm_num at h1 h2 ⊢ 
  <;> try { 
    omega 
  }
  <;> try { 
    have h16 : a = 152 := ha 
    rw [h16]
    all_goals omega
  }