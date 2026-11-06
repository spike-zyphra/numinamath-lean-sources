import Mathlib

theorem number_theory_113343 (a b c d : ℕ) (h₀ : a + b + c + d = 2598)
    (h₁ : Nat.Prime a) (h₂ : ∃ n, b = n ∧ c = n + 1 ∧ d = n + 2) :
    a = 3 ∧ b = 864 ∧ c = 865 ∧ d = 866 := by
  rcases h₂ with ⟨n, h₃, h₄, h₅⟩
  rw [h₃, h₄, h₅] at h₀
  have eq1 : a + 3 * n = 2595 := by
    omega
  have h3 : a % 3 = 0 := by
    omega
  have h4 : a = 3 := by
    by_cases h5 : a > 3
    · -- Assume a > 3
      have h6 : ¬Nat.Prime a := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ a by omega)
        all_goals linarith
      contradiction
    · -- Assume a <= 3
      have h7 : a ≤ 3 := by linarith
      interval_cases a <;> norm_num at h₁ ⊢
      all_goals omega
  have hn : n = 864 := by
    omega
  have hb : b = 864 := by 
    omega
  have hc : c = 865 := by 
    omega
  have hd : d = 866 := by 
    omega
  exact ⟨h4, hb, hc, hd⟩