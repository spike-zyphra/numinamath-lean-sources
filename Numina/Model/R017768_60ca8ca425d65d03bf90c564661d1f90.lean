import Mathlib

theorem number_theory_46011 (n : ℕ) (h₀ : 2 ≤ n) :
    (2^(2^n) + 1) % 10 = 7 := by
  have h1 : ∀ (n : ℕ), 2 ≤ n → (2 ^ (2 ^ n) : ℕ) % 10 = 6 := by
    intro n hn
    have h2 : n ≥ 2 := by linarith
    have base_two : (2 ^ (2 ^ 2) : ℕ) % 10 = 6 := by
      norm_num
    have step : ∀ (k : ℕ), k ≥ 2 → (2 ^ (2 ^ k) : ℕ) % 10 = 6 → (2 ^ (2 ^ (k + 1)) : ℕ) % 10 = 6 := by
      intro k hk h
      have h4 : (2 ^ (2 ^ (k + 1)) : ℕ) = (2 ^ (2 ^ k) ) ^ 2 := by
        ring_nf
      rw [h4]
      simp [Nat.pow_mod, h] at *
      all_goals omega
    exact Nat.le_induction base_two step n h2
  have h2 : (2 ^ (2 ^ n) : ℕ) % 10 = 6 := h1 n h₀
  omega