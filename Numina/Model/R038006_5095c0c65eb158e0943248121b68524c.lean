import Mathlib

theorem number_theory_5462 :
    IsLeast {n | 0 < n ∧ 2019 ∣ ∑ i in Finset.Icc 1 n, i^3} 672 := by 
  constructor
  · -- Show 672 is indeed in the set
    constructor
    · norm_num
    · -- Show that 2019 divides the sum
      native_decide
  · -- Show there is no smaller positive integer in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h 
    push_neg at h 
    have h1 : n < 672 := by linarith
    have h2 : ¬ (2019 ∣ ∑ i in Finset.Icc 1 n, i^3) := by
      interval_cases n <;> try { native_decide }
    exact h2 hn_div