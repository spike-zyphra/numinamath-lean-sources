import Mathlib

theorem number_theory_175323 (n : ℕ) (hn : n > 0) :
    5 ∣ (n - 1) ∨ 5 ∣ n ∨ 5 ∣ (n + 1) ∨ 5 ∣ (n ^ 2 + 1) := by
  have h1 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    omega
  rcases h1 with (h | h | h | h | h)
  · -- Case n ≡ 0 mod 5: $n$ is divisible by 5
    have h2 : 5 ∣ n := by
      exact Nat.dvd_of_mod_eq_zero h
    simp [h2]
  · -- Case n ≡ 1 mod 5: $n - 1$ is divisible by 5
    have h2 : 5 ∣ (n - 1) := by
      omega
    simp [h2]
  · -- Case n ≡ 2 mod 5: $n^2 + 1$ is divisible by 5
    have h2 : 5 ∣ (n ^ 2 + 1) := by
      have h3 : n % 5 = 2 := h
      have h4 : (n ^ 2) % 5 = 4 := by
        simp [Nat.pow_mod, h3]
      have h5 : (n ^ 2 + 1) % 5 = 0 := by
        omega
      exact Nat.dvd_of_mod_eq_zero h5
    simp [h2]
  · -- Case n ≡ 3 mod 5: $n^2 + 1$ is divisible by 5
    have h2 : 5 ∣ (n ^ 2 + 1) := by
      have h3 : n % 5 = 3 := h
      have h4 : (n ^ 2) % 5 = 4 := by
        simp [Nat.pow_mod, h3]
      have h5 : (n ^ 2 + 1) % 5 = 0 := by
        omega
      exact Nat.dvd_of_mod_eq_zero h5
    simp [h2]
  · -- Case n ≡ 4 mod 5: $n + 1$ is divisible by 5
    have h2 : 5 ∣ (n + 1) := by
      omega
    simp [h2]