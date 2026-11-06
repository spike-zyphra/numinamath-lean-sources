import Mathlib

theorem number_theory_116633 :
    IsLeast {n | ∃ k, n = ∑ i ∈ Finset.range 5, (k + i) ∧ ∃ l, n = ∑ i ∈ Finset.range 7, (l + i)} 35 ∧
    IsLeast {n | n > 35 ∧ ∃ k, n = ∑ i ∈ Finset.range 5, (k + i) ∧ ∃ l, n = ∑ i ∈ Finset.range 7, (l + i)} 70 ∧
    IsLeast {n | n > 70 ∧ ∃ k, n = ∑ i ∈ Finset.range 5, (k + i) ∧ ∃ l, n = ∑ i ∈ Finset.range 7, (l + i)} 105 := by

  constructor
  · -- Prove 35 is the least natural number that can be expressed as sum of 5 and sum of 7 consecutive numbers
    constructor
    · -- Show 35 is in the set
      use 5
      constructor
      · -- Show 35 is the sum of 5 consecutive numbers starting from 5
        norm_num [Finset.sum_range_succ]
        <;> try { tauto }
        <;> try { linarith }
        <;> try { ring_nf }
        <;> try { nlinarith }
      · -- Show there exists a number l such that 35 is the sum of 7 consecutive numbers starting from l
        use 2
        norm_num [Finset.sum_range_succ]
        <;> try { tauto }
        <;> try { linarith }
        <;> try { ring_nf }
        <;> try { nlinarith }
        <;> try { native_decide }
    · -- Show no smaller number is in the set
      intro n hn
      rcases hn with ⟨k, hk5, ⟨l, hk7⟩⟩
      norm_num [Finset.sum_range_succ] at hk5 hk7
      have h1 : 35 ∣ n := by
        omega
      have : n ≥ 35 := by
        omega
      linarith

  constructor
  · -- Prove 70 is the least such greater than 35
    constructor
    · -- Show 70 is in the set
      refine ⟨by norm_num, ?_⟩
      use 12
      constructor
      · -- Show 70 is the sum of 5 consecutive numbers starting from 12
        norm_num [Finset.sum_range_succ]
        <;> try { tauto }
        <;> try { linarith }
        <;> try { ring_nf }
        <;> try { nlinarith }
      · -- Show there exists a number l such that 70 is the sum of 7 consecutive numbers starting from l
        use 7
        norm_num [Finset.sum_range_succ]
        <;> try { tauto }
        <;> try { linarith }
        <;> try { ring_nf }
        <;> try { nlinarith }
        <;> try { native_decide }

    · -- Show no smaller number is in the set
      intro n hn
      rcases hn with ⟨hn1, k, hk5, ⟨l, hk7⟩⟩
      norm_num [Finset.sum_range_succ] at hk5 hk7
      have h1 : 35 ∣ n := by
        omega
      have : n ≥ 70 := by
        omega
      linarith

  · -- Prove 105 is the least such greater than 70
    constructor
    · -- Show 105 is in the set
      refine ⟨by norm_num, ?_⟩
      use 19
      constructor
      · -- Show 105 is the sum of 5 consecutive numbers starting from 19
        norm_num [Finset.sum_range_succ]
        <;> try { tauto }
        <;> try { linarith }
        <;> try { ring_nf }
        <;> try { nlinarith }
      · -- Show there exists a number l such that 105 is the sum of 7 consecutive numbers starting from l
        use 12
        norm_num [Finset.sum_range_succ]
        <;> try { tauto }
        <;> try { linarith }
        <;> try { ring_nf }
        <;> try { nlinarith }
        <;> try { native_decide }

    · -- Show no smaller number is in the set
      intro n hn
      rcases hn with ⟨hn1, k, hk5, ⟨l, hk7⟩⟩
      norm_num [Finset.sum_range_succ] at hk5 hk7
      have h1 : 35 ∣ n := by
        omega
      have : n ≥ 105 := by
        omega
      linarith