import Mathlib

theorem number_theory_129964 :
    IsLeast {n | ∃ k, n = ∑ i ∈ Finset.range 9, (k + i) ∧ ∃ m, n = ∑ i ∈ Finset.range 10, (m + i) ∧
      ∃ p, n = ∑ i ∈ Finset.range 11, (p + i)} 495 := by
  constructor
  · -- Show 495 is in the set
    use 51
    constructor
    · -- Show 495 = ∑ i ∈ Finset.range 9, (51 + i)
      norm_num [Finset.sum_range_succ]
      <;> try { omega }
    · -- Show existence of m
      use 45
      constructor
      · -- Show 495 = ∑ i ∈ Finset.range 10, (45 + i)
        norm_num [Finset.sum_range_succ]
        <;> try { omega }
      · -- Show existence of p
        use 40
        all_goals
        · -- Show 495 = ∑ i ∈ Finset.range 11, (40 + i)
          norm_num [Finset.sum_range_succ]
          <;> try { omega }
  · -- Show there is no smaller element in the set
    intro n hn
    rcases hn with ⟨k, hk, m, hm, p, hp⟩
    norm_num [Finset.sum_range_succ] at hk hm hp
    omega