import Mathlib

theorem number_theory_240337 (n : ℕ) (h : Even n) : 8 ∣ n * (n + 2) := by
  rcases h with ⟨k, hk⟩
  have eq1 : n * (n + 2) = 4 * (k * (k + 1)) := by
    rw [hk]
    ring
  rw [eq1]
  have h1 : k * (k + 1) % 2 = 0 := by
    have h2 : k % 2 = 0 ∨ k % 2 = 1 := by
      omega
    rcases h2 with (h3 | h3)
    · -- Case k is even
      simp [Nat.mul_mod, Nat.add_mod, h3]
    · -- Case k is odd
      simp [Nat.mul_mod, Nat.add_mod, h3]
  omega