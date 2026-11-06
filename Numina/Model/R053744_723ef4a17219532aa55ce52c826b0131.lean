import Mathlib

theorem number_theory_317287 (n : ℕ) :
    2 ∣ (n^2 + n + 2) ∧ ¬5 ∣ (n^2 + n + 2) := by
  constructor
  · -- Show that $n^2 + n + 2$ is even
    have h1 : (n ^ 2 + n + 2) % 2 = 0 := by
      have h : n % 2 = 0 ∨ n % 2 = 1 := by
        omega
      rcases h with (h | h)
      · -- If n is even
        simp [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, h]
      · -- If n is odd
        simp [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, h]
    exact Nat.dvd_of_mod_eq_zero h1
  · -- Show that $n^2 + n + 2$ is not divisible by 5
    intro h
    have h1 : (n ^ 2 + n + 2) % 5 = 0 := by
      exact Nat.dvd_iff_mod_eq_zero.mp h
    have h2 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
      omega
    rcases h2 with (h | h | h | h | h)
    · -- Case n ≡ 0 (mod 5)
      norm_num [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, h] at h1
    · -- Case n ≡ 1 (mod 5)
      norm_num [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, h] at h1
    · -- Case n ≡ 2 (mod 5)
      norm_num [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, h] at h1
    · -- Case n ≡ 3 (mod 5)
      norm_num [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, h] at h1
    · -- Case n ≡ 4 (mod 5)
      norm_num [Nat.pow_mod, Nat.add_mod, Nat.mul_mod, h] at h1