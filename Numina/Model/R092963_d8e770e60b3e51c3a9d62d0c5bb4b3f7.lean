import Mathlib

theorem number_theory_110818 (p : ℕ) (hp : Nat.Prime p) (h : Even p) : p = 2 := by
  have h2 : p % 2 = 0 := by
    exact Nat.even_iff.1 h
  by_cases h3 : p ≤ 2
  · interval_cases p <;> tauto
  · -- Case p > 2
    push_neg at h3
    have h4 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals linarith
    contradiction