import Mathlib

theorem number_theory_134284 {d m n : ℕ} (hd : d ≠ 0) (hmn : d ∣ m + 2019 * n ∧ d ∣ n + 2019 * m) :
    d ∣ 2019 * (m + 2019 * n) - (n + 2019 * m) := by
  have h1 : d ∣ m + 2019 * n := hmn.1
  have h2 : d ∣ n + 2019 * m := hmn.2

  have h3 : d ∣ 2019 * (m + 2019 * n) := by
    apply dvd_mul_of_dvd_right
    exact h1
    all_goals omega

  have h4 : d ∣ (n + 2019 * m) := by
    exact h2

  apply Nat.dvd_sub'
  exact h3
  exact h4
  all_goals omega