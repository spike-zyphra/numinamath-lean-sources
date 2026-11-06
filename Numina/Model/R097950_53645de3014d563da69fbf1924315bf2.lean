import Mathlib

theorem algebra_20999 : IsGreatest {p | p.Prime ∧ p < 100} 97 ∧
    IsGreatest {p | p.Prime ∧ p ∣ Nat.factorial 97} 97 := by 
  constructor 
  · constructor 
    · constructor 
      · norm_num 
      · norm_num 
    · intro a h 
      have ⟨ha1, ha2⟩ := h
      by_contra h'
      push_neg at h'
      have h3 : a < 100 := ha2
      have h4 : a > 97 := by 
        nlinarith 
      interval_cases a <;> norm_num at ha1 <;> all_goals contradiction
  · constructor 
    · constructor 
      · norm_num 
      · native_decide 
    · intro a h 
      have ⟨ha1, ha2⟩ := h 
      by_contra h'
      push_neg at h'
      have h3 : a > 97 := by linarith 
      have h4 : a ∣ Nat.factorial 97 := ha2 
      have h5 : a.Prime := ha1 
      have h6 : a ≤ 97 := by 
        have h7 : a ∣ Nat.factorial 97 := h4 
        have h8 : a.Prime := h5 
        have h9 : a ≤ 97 := by 
          apply (Nat.Prime.dvd_factorial h8).mp 
          exact h7 
        linarith 
      linarith