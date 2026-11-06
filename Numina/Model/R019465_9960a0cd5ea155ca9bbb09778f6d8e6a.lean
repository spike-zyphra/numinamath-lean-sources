import Mathlib

theorem number_theory_170604 (m n : ℕ) (h₀ : 100 ≤ m ∧ m < 1000) (h₁ : 100 ≤ n ∧ n < 1000)
    (h₂ : m - n = 889) (h₃ : (Nat.digits 10 m).sum - (Nat.digits 10 n).sum = 25) :
    (m = 999 ∧ n = 110) ∨ (m = 989 ∧ n = 100) := by
  rcases h₀ with ⟨hm1, hm2⟩
  rcases h₁ with ⟨hn1, hn2⟩
  have h4 : m = n + 889 := by
    omega
  have h5 : n ≤ 110 := by
    omega
  have h6 : n ≥ 100 := by
    omega
  interval_cases n <;> norm_num [h4] at *
  <;> omega