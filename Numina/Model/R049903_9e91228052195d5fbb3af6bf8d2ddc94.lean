import Mathlib

theorem number_theory_9818 :
  IsLeast {n : ℕ | n.Prime ∧ (∃ p q r : ℕ , p ≠ q ∧ q ≠ r ∧ r ≠ p ∧ p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n) ∧ n ∈ Finset.Icc 100 999} 101 := by
  constructor
  · -- Show that 101 is in the set
    constructor
    · norm_num
    constructor
    · use 3, 19, 79
      constructor
      · norm_num -- p ≠ q
      constructor
      · norm_num -- q ≠ r
      constructor
      · norm_num -- r ≠ p
      constructor
      · norm_num -- p is prime
      constructor
      · norm_num -- q is prime
      constructor
      · norm_num -- r is prime
      all_goals norm_num -- p + q + r = n
    · -- Show 101 ∈ Finset.Icc 100 999
      simp [Finset.mem_Icc]
  · -- Show that 101 is the least element in the set
    intro n hn
    rcases hn with ⟨hn_prime, ⟨p, q, r, hpq, hqr, hprp, hp_prime, hq_prime, hr_prime, heq⟩, hn_range⟩
    rw [Finset.mem_Icc] at hn_range
    rcases hn_range with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    have hn3 : n = 100 := by linarith
    rw [hn3] at heq hn_prime
    norm_num at hn_prime
    all_goals
      try linarith
      <;> norm_num [Nat.Prime] at hp_prime hq_prime hr_prime
      <;> omega