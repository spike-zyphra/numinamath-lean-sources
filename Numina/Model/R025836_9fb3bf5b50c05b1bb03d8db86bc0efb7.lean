import Mathlib

theorem number_theory_243268 (t : ℕ) (ht : t > 0) (h : 2 * t ^ 2 - 34 * t = 60) :
    t = 10 := by 
  have h1 : t ≤ 34 := by
    by_contra h1
    push_neg at h1
    have eq1 : t ≥ 35 := by omega
    have eq3 : 2 * t ^ 2 ≥ 34 * t + 76 := by
      nlinarith [show (t : ℕ) ≥ 35 by omega, sq_nonneg (t - 19 : ℤ), sq_nonneg (t - 18 : ℤ)]
    have eq4 : 2 * t ^ 2 - 34 * t ≥ 76 := by
      omega
    have eq5 : 2 * t ^ 2 - 34 * t = 60 := by 
      exact_mod_cast h
    omega
  interval_cases t <;> omega