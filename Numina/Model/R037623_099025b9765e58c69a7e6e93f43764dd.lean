import Mathlib

theorem number_theory_316313 {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hsum : p + q = 2019) : (p - 1) ^ (q - 1) = 1 ∨ (p - 1) ^ (q - 1) = 2016 := by
  have h1 : p ≤ 2019 := by
    linarith
  have h2 : q ≤ 2019 := by
    linarith
  by_cases h3 : p % 2 = 1
  · -- Assume p is odd, then q must be even
    have h4 : q % 2 = 0 := by
      omega
    have h5 : q = 2 := by
      by_cases h6 : q > 2
      · -- Assume q > 2, then q is not prime
        have h7 : ¬Nat.Prime q := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega)
          all_goals linarith
        contradiction
      · -- Assume q ≤ 2
        interval_cases q <;> norm_num at *
    have h5' : p = 2017 := by
      omega
    right
    rw [h5', h5]
    all_goals
      norm_num
  · -- Assume p is even
    have h6 : p % 2 = 0 := by
      omega
    have h7 : p = 2 := by
      by_cases h8 : p > 2
      · -- Assume p > 2, then p is not prime
        have h8' : ¬Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals linarith
        contradiction
      · -- Assume p ≤ 2
        interval_cases p <;> norm_num at *
    have h7' : q = 2017 := by
      omega
    left
    rw [h7, h7']
    all_goals
      norm_num