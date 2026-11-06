import Mathlib

theorem number_theory_174703 :
    ¬∃ n : ℕ, ∃ k : ℕ, n^2 ≡ k [MOD 3] ∧ k = 2 := by
  rintro ⟨n, ⟨k, h1, h2⟩⟩
  rw [h2] at h1
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    omega
  rcases h with (h | h | h)
  · -- Case n % 3 = 0
    have h3 : (n ^ 2) % 3 = 0 := by
      simp [Nat.pow_mod, h]
    have h4 : (n ^ 2) % 3 = 2 := by
      simp [Nat.ModEq] at h1
      omega
    omega
  · -- Case n % 3 = 1
    have h3 : (n ^ 2) % 3 = 1 := by
      simp [Nat.pow_mod, h]
    have h4 : (n ^ 2) % 3 = 2 := by
      simp [Nat.ModEq] at h1
      omega
    omega
  · -- Case n % 3 = 2
    have h3 : (n ^ 2) % 3 = 1 := by
      simp [Nat.pow_mod, h]
    have h4 : (n ^ 2) % 3 = 2 := by
      simp [Nat.ModEq] at h1
      omega
    omega