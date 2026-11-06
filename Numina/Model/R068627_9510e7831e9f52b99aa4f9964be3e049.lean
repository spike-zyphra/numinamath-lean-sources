import Mathlib

theorem number_theory_311202 {m : ℕ} (h1 : m / 10000 + m % 10000 = 18889) (h2 : m / 100000 + m % 100000 = 58741) :
    (m / 100) % 10 = 6 := by
  omega