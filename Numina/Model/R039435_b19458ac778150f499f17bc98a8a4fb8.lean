import Mathlib

theorem number_theory_11773 :
    IsLeast {n : ℕ | ∃ k, n = ∑ i ∈ Finset.range 9, (k + i) ∧
      ∃ m, n = ∑ j ∈ Finset.range 10, (m + j) ∧
      ∃ p, n = ∑ l ∈ Finset.range 11, (p + l)} 495 := by
  constructor
  · -- First, prove 495 is in the set
    use 51
    constructor
    · -- Show 495 = ∑ i ∈ Finset.range 9, (51 + i)
      native_decide
    use 45
    constructor
    · -- Show 495 = ∑ j ∈ Finset.range 10, (45 + j)
      native_decide
    use 40
    · -- Show 495 = ∑ l ∈ Finset.range 11, (40 + l)
      native_decide
  · -- Now, prove 495 is the smallest
    intro n hn
    rcases hn with ⟨k, h9, m, h10, p, h11⟩
    have eq1 : n = 9 * k + 36 := by
      norm_num [Finset.sum_range_succ] at h9
      omega
    have eq2 : n = 10 * m + 45 := by
      norm_num [Finset.sum_range_succ] at h10
      omega
    have eq3 : n = 11 * p + 55 := by
      norm_num [Finset.sum_range_succ] at h11
      omega
    omega