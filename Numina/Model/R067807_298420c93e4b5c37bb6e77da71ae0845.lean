import Mathlib

theorem number_theory_233513 (n : ℕ) (h₀ : n < 100000) (h₁ : Nat.Prime (n / 10000)) (h₂ : Nat.Prime (n % 10000))
    (h₃ : ∃ m, m^2 = n / 10000) (h₄ : Even (Nat.ofDigits 10 [n % 10000, n / 10000])) :
    n = 26116 := by
  rcases h₃ with ⟨m, hm⟩
  have h5 : n / 10000 ≤ 9 := by
    have h6 : n < 100000 := h₀
    omega
  have h6 : m ≤ 3 := by nlinarith [hm, h5]
  interval_cases m <;> interval_cases h7 : n / 10000 <;> norm_num at hm h₁ <;> omega