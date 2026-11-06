import Mathlib

theorem number_theory_98720 (t c : ℕ) (ht : t > 0) (hc : c > 0)
    (h1 : 5 * t = 3 * c + 1) (h2 : 2 * c = 3 * t + 1) (h3 : c = 50) :
    t = 10 := by
  rw [h3] at h1 h2
  omega