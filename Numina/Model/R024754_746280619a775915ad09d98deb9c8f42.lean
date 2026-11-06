import Mathlib

theorem number_theory_165084 (m n k : ℕ) (hm : m > 0) (hn : n > 0) (hk : k > 0)
    (hmn : m + n = 2021) (hprime1 : Nat.Prime (m - 3 * k)) (hprime2 : Nat.Prime (n + k)) :
    m + 2 * n + 3 * k = 2025 ∨ m + 2 * n + 3 * k = 4040 := by
  by_cases h : m - 3 * k ≤ 2
  · -- Case where m - 3k ≤ 2
    interval_cases h' : m - 3 * k <;> norm_num at hprime1 <;> omega
  · -- Case where m - 3k > 2
    by_cases h' : n + k ≤ 2
    · -- Case where n + k ≤ 2
      interval_cases h'' : n + k <;> norm_num at hprime2 <;> omega
    · -- Case where both m - 3k > 2 and n + k > 2
      have h2 : (m - 3 * k) % 2 = 1 := by
        by_contra h'
        push_neg at h'
        have h'' : ¬ Nat.Prime (m - 3 * k) := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (m - 3 * k) by omega)
          all_goals omega
        contradiction
      have h3 : (n + k) % 2 = 1 := by
        by_contra h'
        push_neg at h'
        have h'' : ¬ Nat.Prime (n + k) := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ (n + k) by omega)
          all_goals omega
        contradiction
      have h4 : (m + n) % 2 = 1 := by
        omega
      omega