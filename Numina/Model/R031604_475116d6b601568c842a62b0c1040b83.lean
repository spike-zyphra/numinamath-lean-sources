import Mathlib

theorem number_theory_275405 (n : ℕ) : Even (n * (n + 1)) := by
  have h1 : n * (n + 1) % 2 = 0 := by
    have h2 : n % 2 = 0 ∨ n % 2 = 1 := by
      omega
    rcases h2 with (h2 | h2)
    ·
      simp [Nat.mul_mod, Nat.add_mod, h2]
    ·
      simp [Nat.mul_mod, Nat.add_mod, h2]
  exact ⟨n * (n + 1) / 2, by
    omega⟩