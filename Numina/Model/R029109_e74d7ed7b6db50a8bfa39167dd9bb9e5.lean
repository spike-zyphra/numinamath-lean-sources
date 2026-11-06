import Mathlib

theorem number_theory_106357 :
    ∀ n : ℕ, (Even n ∧ Even (n + 2)) → 8 ∣ n * (n + 2) := by
  intro n h
  rcases h with ⟨hn1, hn2⟩
  have h1 : n % 2 = 0 := by 
    obtain ⟨k, hk⟩ := hn1
    omega
  have h2 : n % 8 = 0 ∨ n % 8 = 2 ∨ n % 8 = 4 ∨ n % 8 = 6 := by
    omega
  rcases h2 with (h2 | h2 | h2 | h2)
  · -- n ≡ 0 (mod 8)
    have h3 : (n * (n + 2)) % 8 = 0 := by
      simp [Nat.mul_mod, Nat.add_mod, h2]
    have : 8 ∣ n * (n + 2) := by
      omega
    assumption
  · -- n ≡ 2 (mod 8)
    have h3 : (n * (n + 2)) % 8 = 0 := by
      simp [Nat.mul_mod, Nat.add_mod, h2]
    have : 8 ∣ n * (n + 2) := by
      omega
    assumption
  · -- n ≡ 4 (mod 8)
    have h3 : (n * (n + 2)) % 8 = 0 := by
      simp [Nat.mul_mod, Nat.add_mod, h2]
    have : 8 ∣ n * (n + 2) := by
      omega
    assumption
  · -- n ≡ 6 (mod 8)
    have h3 : (n * (n + 2)) % 8 = 0 := by
      simp [Nat.mul_mod, Nat.add_mod, h2]
    have : 8 ∣ n * (n + 2) := by
      omega
    assumption