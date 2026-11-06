import Mathlib

theorem number_theory_197060 (n : ℕ) : ¬ ∃ m, m^2 = 6 * n + 2 := by
  rintro ⟨m, hm⟩
  have h1 : m ^ 2 % 6 = 2 := by
    omega
  have h2 : m % 6 = 0 ∨ m % 6 = 1 ∨ m % 6 = 2 ∨ m % 6 = 3 ∨ m % 6 = 4 ∨ m % 6 = 5 := by
    omega
  rcases h2 with (h | h | h | h | h | h)
  · -- if m ≡ 0 [MOD 6]
    simp [Nat.pow_mod, h] at h1
    all_goals omega
  · -- if m ≡ 1 [MOD 6]
    simp [Nat.pow_mod, h] at h1
    all_goals omega
  · -- if m ≡ 2 [MOD 6]
    simp [Nat.pow_mod, h] at h1
    all_goals omega
  · -- if m ≡ 3 [MOD 6]
    simp [Nat.pow_mod, h] at h1
    all_goals omega
  · -- if m ≡ 4 [MOD 6]
    simp [Nat.pow_mod, h] at h1
    all_goals omega
  · -- if m ≡ 5 [MOD 6]
    simp [Nat.pow_mod, h] at h1
    all_goals omega