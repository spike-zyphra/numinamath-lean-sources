import Mathlib

theorem number_theory_137297 (v z : ℕ) (h : v > 0) (hz : z > 0)
    (h1 : v * 28 = z * 70) (h2 : v * 70 = z * 28) :
    {m | ∃ n, m = n * v ∧ m > 0}.encard = 6 := by
  nlinarith