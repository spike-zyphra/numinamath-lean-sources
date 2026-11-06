import Mathlib

theorem algebra_21182 : IsLeast {n : ℕ | n > 2006 ∧ gcd (n / 10) (n % 10) > 1 ∧ Odd n} 2013 := by
  constructor
  · -- Show 2013 is in the set
    constructor
    · -- Show 2013 > 2006
      norm_num
    constructor
    · -- Show gcd (2013 / 10) (2013 % 10) > 1
      native_decide
    · -- Show Odd 2013
      decide
  · -- Show no smaller element is in the set
    intro n hn
    rcases hn with ⟨h1, h2, h3⟩
    by_contra h
    push_neg at h
    have h4 : n > 2006 := h1
    have h5 : n < 2013 := by linarith
    have h6 : n % 2 = 1 := by
      have h7 : Odd n := h3
      rcases h7 with ⟨k, hk⟩
      omega
    interval_cases n <;> norm_num [gcd] at h2 ⊢ <;> try { contradiction }