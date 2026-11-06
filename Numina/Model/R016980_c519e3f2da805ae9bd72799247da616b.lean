import Mathlib

theorem number_theory_232339 (n : ℕ) (h₀ : n < 10000000) (h₁ : ∃ k, n = k * 1111111) (h₂ : ∃ m, n = m * 111111) (h₃ : (Nat.digits 10 n).sum < 100) (h₄ : (Nat.digits 10 n).sum > 9)
    (h₅ : (Nat.digits 10 n).headI = (Nat.digits 10 n).tail.tail.headI) (h₆ : (Nat.digits 10 n).tail.headI = (Nat.digits 10 n).tail.tail.tail.headI) :
    n = 3337777 := by
  rcases h₁ with ⟨k, hk⟩
  rcases h₂ with ⟨m, hm⟩
  have h7 : k * 1111111 = m * 111111 := by 
    linarith [hk, hm]
  have h9 : k = 0 := by 
    omega
  have h10 : n = 0 := by
    linarith [h9, hk]
  rw [h10] at h₃ h₄
  all_goals
    norm_num at h₃ h₄
    all_goals omega