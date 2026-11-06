import Mathlib

theorem number_theory_311006 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a = 2 * b) (h2 : b = c - 7) (h3 : Nat.Prime (a + b + c)) (h4 : a + b + c < 70)
    (h5 : (Nat.digits 10 (a + b + c)).sum = 13) :
    a = 30 ∧ b = 15 ∧ c = 22 := by
  have h6 : c = b + 7 := by 
    omega
  have h7 : a + b + c = 4 * b + 7 := by 
    rw [show a = 2 * b by linarith [h1], show c = b + 7 by linarith [h6]]
    omega
  have h8 : a + b + c < 70 := h4
  have h9 : a + b + c = 67 := by
    interval_cases h : a + b + c <;> norm_num at h3 h4 h5 ⊢ <;> try { 
      all_goals tauto
    }
    <;> try { 
      omega
    }
  have h10 : 4 * b + 7 = 67 := by
    linarith [h7, h9]
  have h11 : b = 15 := by
    omega
  have h12 : a = 30 := by 
    linarith [h1, h11]
  have h13 : c = 22 := by 
    linarith [h6, h11]
  exact ⟨by linarith, by linarith, by linarith⟩