import Mathlib

theorem number_theory_3843 :
    IsLeast {n | ∃ k, n = k + 22 ∧ ∃ m, m > 0 ∧ m^2 = ∑ i ∈ Finset.range 23, (k + i)} 34 := by
  constructor
  · -- Prove that 34 is in the set
    use 12
    constructor
    · -- Show that 34 = 12 + 22
      norm_num
    · -- Show the existence of a positive integer m
      use 23
      constructor
      · -- Show 23 > 0
        norm_num
      · -- Show 23^2 equals the sum
        norm_num [Finset.sum_range_succ]
  · -- Now prove that 34 is the least element
    intro n hn
    rcases hn with ⟨k, hk, m, hm, h⟩
    by_contra h'
    push_neg at h'
    have h1 : k < 12 := by omega
    have eq : m^2 = 23 * k + 253 := by 
      simp [Finset.sum_range_succ] at h 
      nlinarith
    have h2 : m ≤ 22 := by
      nlinarith
    interval_cases m <;> omega