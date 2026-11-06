import Mathlib

theorem number_theory_289491 : IsLeast {x | x.Prime ∧ x > 50} 53 := by 
  constructor
  · -- Show 53 is in the set, i.e., it is prime and greater than 50.
    constructor
    · -- Show 53 is prime
      norm_num
    · -- Show 53 > 50
      norm_num
  · -- Show that 53 is the least element in the set.
    intro x hx
    rcases hx with ⟨h_prime, h_gt⟩
    by_contra h
    push_neg at h 
    have h1 : x > 50 := h_gt
    have h2 : x < 53 := h
    have h3 : x = 51 ∨ x = 52 := by 
      omega
    rcases h3 with (r | r)
    · -- Case x = 51
      rw [r] at h_prime
      norm_num at h_prime
    · -- Case x = 52
      rw [r] at h_prime
      norm_num at h_prime