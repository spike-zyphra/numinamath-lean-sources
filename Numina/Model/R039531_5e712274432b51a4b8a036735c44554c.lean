import Mathlib

theorem number_theory_267072 {n : ℤ} (hn : n > 0) :
    (n / 10 - 2 * (n % 10)) % 7 = 0 → n % 7 = 0 ∧
    (n / 10 - 2 * (n % 10)) % 7 ≠ 0 → n % 7 ≠ 0 := by
  intro h1 h2
  have h3 : (n / 10 - 2 * (n % 10)) % 7 = 0 := h1
  have h4 : n % 7 = 0 := h2.1
  have h5 : (n / 10 - 2 * (n % 10)) % 7 ≠ 0 := h2.2
  contradiction