import Mathlib

theorem number_theory_308597 {p : ℕ} (hp : p.Prime) (hp2 : (p + 2).Prime)
    (h : 3 < p) (h' : 3 < p + 2) : 6 ∣ (p + 1) := by
  have hp2' : p % 2 = 1 := by
    by_contra h'
    push_neg at h'
    have h2 : p % 2 = 0 := by
      omega
    have h3 : 2 ∣ p := by
      omega
    have h4 : ¬ p.Prime := by
      apply Nat.not_prime_of_dvd_of_lt h3 (by omega) (by omega)
    contradiction
  have hp3 : p % 3 = 2 := by
    have h1 : p % 3 = 1 ∨ p % 3 = 2 := by
      have h4 : p % 3 = 1 ∨ p % 3 = 2 ∨ p % 3 = 0 := by
        omega
      rcases h4 with (h4 | h4 | h4)
      · exact Or.inl h4
      · exact Or.inr h4
      · 
        have h5 : 3 ∣ p := by
          omega
        have h6 : ¬ p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt h5 (by omega) (by omega)
        contradiction
    rcases h1 with (h1 | h1)
    · -- Assume p ≡ 1 (mod 3)
      exfalso
      have h4 : (p + 2) % 3 = 0 := by
        omega
      have h5 : 3 ∣ (p + 2) := by
        omega
      have h6 : ¬(p + 2).Prime := by
        apply Nat.not_prime_of_dvd_of_lt h5 (by omega) (by omega)
      contradiction
    · -- p ≡ 2 (mod 3)
      exact h1
  have hp4 : p % 6 = 5 := by
    omega
  omega