import Mathlib

theorem number_theory_259269 (p : ℕ) (hp : Nat.Prime p) :
    Nat.Prime (p^2 + 2) ↔ p = 3 := by
  constructor
  · -- Assume $p$ is prime and $p^2 + 2$ is prime, prove $p = 3$.
    intro h
    by_cases h1 : p ≤ 3
    · -- If $p \leq 3$, and $p$ is prime, then $p$ is 2 or 3.
      interval_cases p <;> norm_num at hp h ⊢ <;> try { contradiction }
      <;> try { tauto }
    · -- Case $p > 3$
      have h2 : p % 3 = 1 ∨ p % 3 = 2 := by
        have h3 : p % 3 ≠ 0 := by
          by_contra h4
          have : 3 ∣ p := by
            omega
          have h7 : ¬ Nat.Prime p := by
            apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
            all_goals omega
          contradiction
        omega
      have h3 : (p ^ 2) % 3 = 1 := by
        rcases h2 with (h2 | h2)
        · -- p % 3 = 1
          simp [Nat.pow_mod, h2]
        · -- p % 3 = 2
          simp [Nat.pow_mod, h2]
      have h4 : (p ^ 2 + 2) % 3 = 0 := by
        omega
      have h5 : ¬ Nat.Prime (p^2 + 2) := by
        apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ (p^2 + 2) by omega)
        all_goals nlinarith [show p ≥ 4 by omega]
      contradiction
  · -- Assume $p = 3$, prove $\operatorname{Nat.Prime}\left(p^{2} + 2\right)$.
    intro h
    rw [h]
    norm_num