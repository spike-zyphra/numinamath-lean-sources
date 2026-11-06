import Mathlib

theorem number_theory_181983 (n : ℕ) (h₀ : n % 1000 = n / 10) (h₁ : (Nat.digits 10 n).sum = 22)
    (h₂ : 10 * n + (n / 1000) % 1000 = n - 1998) :
    n = 7555 := by 
  have h3 : n ≥ 1998 := by
    by_contra h
    push_neg at h
    have h4 : n < 1998 := by linarith
    have h6 : n - 1998 = 0 := by 
      omega 
    have h7 : 10 * n + (n / 1000) % 1000 = 0 := by
      omega 
    have h8 : n = 0 := by
      omega 
    have h9 : (Nat.digits 10 n).sum = 0 := by 
      rw [h8]
      norm_num 
      all_goals linarith 
    omega 
  have h4 : n ≥ 1998 := h3 
  exfalso 
  have h5 : n ≤ 1997 := by
    omega
  omega 
  all_goals linarith 
  all_goals omega