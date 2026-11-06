import Mathlib

theorem number_theory_198859 (n : ℕ) (h₀ : Even n) (h₁ : n % 10 ≠ 0) :
    (n ^ 4) % 10 = 6 := by
  have h_n_mod_2 : n % 2 = 0 := by
    obtain ⟨k, hk⟩ := h₀ -- n is even, so n = 2k for some k
    omega -- from n = 2k, derive n % 2 = 0
  have h2 : n % 10 = 2 ∨ n % 10 = 4 ∨ n % 10 = 6 ∨ n % 10 = 8 := by
    omega
  rcases h2 with (h | h | h | h)
  · -- Case n % 10 = 2
    simp [Nat.pow_mod, h]
    all_goals omega
  · -- Case n % 10 = 4
    simp [Nat.pow_mod, h]
    all_goals omega
  · -- Case n % 10 = 6
    simp [Nat.pow_mod, h]
    all_goals omega
  · -- Case n % 10 = 8
    simp [Nat.pow_mod, h]
    all_goals omega