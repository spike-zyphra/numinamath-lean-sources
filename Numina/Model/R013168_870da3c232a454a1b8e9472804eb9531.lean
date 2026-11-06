import Mathlib

theorem number_theory_159767 (n : ℕ) (h₀ : n < 1000000) (h₁ : ∀ i k, i > k → (n / 10 ^ i) % 10 > (n / 10 ^ k) % 10)
    (h₂ : 10 ^ 98 < n ^ (Nat.digits 10 n).sum ∧ n ^ (Nat.digits 10 n).sum < 10 ^ 99) :
    n = 653210 := by 
  have h3 := h₁ 6 5 (by norm_num)
  norm_num at h3 
  all_goals 
    omega