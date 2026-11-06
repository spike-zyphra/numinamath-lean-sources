import Mathlib

theorem number_theory_1260 {n : ℕ} (h0 : n < 100) (h1 : n > 9) (h : 10 * (n % 10) + (n / 10) = 3 * ((n : ℕ) / 10 + (n : ℕ) % 10)) : n = 72 := by
  interval_cases n <;> try { simp_all }
  <;> omega