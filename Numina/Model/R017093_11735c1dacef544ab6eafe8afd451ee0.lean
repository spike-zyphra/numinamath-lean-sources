import Mathlib

theorem number_theory_256 (n : ℕ) (hdigit : (n / 100) % 10 = (n % 10) + 2)
    (h : (n / 100) < 10) (h' : (n % 10) < 10) :
    (n - (100 * (n % 10) + 10 * ((n / 10) % 10) + (n / 100))) % 10 = 8 := by
  have h5 : n < 1000 := by
    omega
  interval_cases n <;> norm_num at hdigit ⊢
    <;> omega