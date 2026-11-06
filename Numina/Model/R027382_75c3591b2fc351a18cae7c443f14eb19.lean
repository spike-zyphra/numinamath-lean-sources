import Mathlib

theorem number_theory_101638 : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p > n := by
  intro n
  have h2 : ∃ p, p > n ∧ p.Prime := by
    have h1 := Nat.exists_infinite_primes (n + 1)
    rcases h1 with ⟨p, hp1, hp2⟩
    have hp3 : p > n := by
      omega
    exact ⟨p, And.intro hp3 hp2⟩
  rcases h2 with ⟨p, hp1, hp2⟩
  exact ⟨p, And.intro hp2 hp1⟩