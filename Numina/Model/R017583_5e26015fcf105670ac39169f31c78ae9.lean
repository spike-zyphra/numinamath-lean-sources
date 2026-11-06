import Mathlib

def is_special (n : ℕ) (a b : ℕ) := a > 2 ∧ b > 0 ∧ n % a = b ∧ n % b = a - 2

theorem number_theory_7636 : ¬∃ n a b, is_special n a b ∧ n = 129 := by 
  rintro ⟨n, a, b, ⟨ha, hb, h1, h2⟩, hn⟩
  rw [hn] at h1 h2
  have h3 : b < a := by
    have h1' : 129 % a = b := by 
      simpa using h1
    have h5 : 129 % a < a := by
      apply Nat.mod_lt
      all_goals omega 
    omega 
  have h4 : a ≤ 129 := by 
    by_contra h 
    push_neg at h 
    have h5 : 129 % a = 129 := by 
      rw [Nat.mod_eq_of_lt]
      all_goals linarith 
    have h6 : b = 129 := by
      omega 
    have h7 : 129 % 129 = a - 2 := by 
      rw [show b = 129 by omega] at h2 
      all_goals omega 
    omega 
  have h5 : a - 2 < b := by
    have h7 : 129 % b < b := by
      apply Nat.mod_lt
      all_goals omega 
    omega 
  have h6 : b = a - 1 := by 
    omega 
  rw [show b = a - 1 by omega] at h2
  interval_cases a <;> omega