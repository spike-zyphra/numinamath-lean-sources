import Mathlib

theorem number_theory_160413 (n : ℕ) (hn : 2 ≤ n) :
    ∃ k, ¬∃ p, p.Prime ∧ p ∈ Finset.Icc k (k + n - 1) := by
  use (Nat.factorial (n + 1) + 2)
  intro h
  rcases h with ⟨p, hp, hp2⟩
  rw [Finset.mem_Icc] at hp2
  rcases hp2 with ⟨h1, h2⟩
  have h3 : p ≤ Nat.factorial (n + 1) + n + 1 := by
    omega
  have h4 : p ≥ Nat.factorial (n + 1) + 2 := by
    omega
  let i := p - Nat.factorial (n + 1)
  have h7 : i ≥ 2 := by
    omega
  have h8 : i ≤ n + 1 := by
    omega
  have h9 : p = Nat.factorial (n + 1) + i := by
    omega
  have h10 : i ∣ Nat.factorial (n + 1) := by
    apply Nat.dvd_factorial
    all_goals
      omega
  have h11 : i ∣ p := by
    rw [h9]
    have : i ∣ (Nat.factorial (n + 1) + i) := by
      apply Nat.dvd_add
      exact h10
      exact Nat.dvd_refl i
    assumption
  have h12 : i < p := by
    nlinarith [h9, Nat.factorial_pos (n + 1)]
  have h13 : i > 1 := by
    omega
  have h14 : i < p := by
    nlinarith
  have h15 : ¬Nat.Prime p := by
    apply Nat.not_prime_of_dvd_of_lt h11
    all_goals
      try linarith
    all_goals
      try linarith
  contradiction