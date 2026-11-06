import Mathlib

theorem number_theory_122733 (p k : ℕ) (hp : p.Prime) (hk : 0 < k ∧ k < p) :
    p ∣ (Nat.factorial p) / (Nat.factorial k * Nat.factorial (p - k)) := by
  have h2 : p ∣ p.choose k := by
    apply hp.dvd_choose_self
    all_goals omega
  have h10 : p.choose k = (Nat.factorial p) / (Nat.factorial k * Nat.factorial (p - k)) := by
    rw [Nat.choose_eq_factorial_div_factorial]
    all_goals
      try nlinarith [hp.one_lt, hk.1, hk.2]
      try {
        apply Nat.factorial_dvd_factorial
        all_goals
          nlinarith
      }
      try omega
  rw [h10] at h2
  exact h2