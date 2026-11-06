import Mathlib

theorem number_theory_256292 : IsGreatest {p | p.Prime ∧ p ∣ 2006} 59 := by
  constructor
  · refine ⟨by norm_num, by norm_num⟩
  · intro p hp
    rcases hp with ⟨prime_p, dvd_p⟩
    have : p ≤ 2006 := by
      exact Nat.le_of_dvd (by norm_num) dvd_p
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at *