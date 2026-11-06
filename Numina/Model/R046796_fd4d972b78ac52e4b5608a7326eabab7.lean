import Mathlib

theorem number_theory_23051 : IsGreatest {d : ℕ | ∀ n : ℕ, 0 < n → d ∣ n * (n + 1) * (n + 2) * (n + 3)} 24 := by
  constructor
  · -- First part: show that 24 is in the set
    show ∀ n : ℕ, 0 < n → 24 ∣ n * (n + 1) * (n + 2) * (n + 3)
    intro n hn
    have h1 : n * (n + 1) * (n + 2) * (n + 3) % 24 = 0 := by
      have h2 : n % 24 = 0 ∨ n % 24 = 1 ∨ n % 24 = 2 ∨ n % 24 = 3 ∨ n % 24 = 4 ∨ n % 24 = 5 ∨
                n % 24 = 6 ∨ n % 24 = 7 ∨ n % 24 = 8 ∨ n % 24 = 9 ∨ n % 24 = 10 ∨ n % 24 = 11 ∨
                n % 24 = 12 ∨ n % 24 = 13 ∨ n % 24 = 14 ∨ n % 24 = 15 ∨
                n % 24 = 16 ∨ n % 24 = 17 ∨ n % 24 = 18 ∨ n % 24 = 19 ∨
                n % 24 = 20 ∨ n % 24 = 21 ∨ n % 24 = 22 ∨ n % 24 = 23 := by
        omega
      rcases h2 with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) <;> simp [h, Nat.mul_mod, Nat.add_mod]
    exact Nat.dvd_of_mod_eq_zero h1
  · -- Second part: show that 24 is greatest in the set
    intro d hd
    have h1 : d ∣ 1 * (1 + 1) * (1 + 2) * (1 + 3) := by
      apply hd 1
      all_goals norm_num
    have h2 : d ∣ 24 := by
      norm_num at h1 ⊢
      exact h1
    have h3 : d ≤ 24 := by
      exact Nat.le_of_dvd (show 0 < (24 : ℕ) by norm_num) h2
    linarith