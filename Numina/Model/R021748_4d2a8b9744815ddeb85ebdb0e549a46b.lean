import Mathlib

theorem number_theory_9592 :
    IsGreatest {n | n.Prime ∧ n ∈ Finset.Icc 10 99 ∧ ∃ p q r s : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧ n = p + q + r + s} 97 := by
  constructor
  · -- Show that 97 is in the set.
    constructor
    · -- Show that 97 is prime.
      norm_num
    constructor
    · -- Show that 97 is in the range [10, 99].
      norm_num
    · -- Show that 97 can be written as the sum of four primes.
      use 2, 3, 3, 89
      all_goals norm_num
  · -- Show that 97 is greatest in the set.
    intro n hn
    rcases hn with ⟨hn_prime, hn_range, ⟨p, hp_prime, q, hq_prime, r, hr_prime, s, hs_prime, hn_eq⟩⟩
    rw [Finset.mem_Icc] at hn_range
    rcases hn_range with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    have h1 : n = 98 ∨ n = 99 := by 
      omega
    rcases h1 with (h1 | h1)
    · -- Assume n = 98
      rw [h1] at hn_prime
      norm_num at hn_prime 
    · -- Assume n = 99 
      rw [h1] at hn_prime 
      norm_num at hn_prime