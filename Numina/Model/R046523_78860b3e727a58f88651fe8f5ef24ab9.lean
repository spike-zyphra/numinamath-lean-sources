import Mathlib

theorem number_theory_19215 :
    IsLeast {n | ∃ k, n = ∑ i ∈ Finset.range 4, (2 * i + 2 * k) ∧ (∃ m, m ^ 2 = n) ∧ (∀ i ∈ Finset.range 4, 0 < (2 * i + 2 * k))} 36 := by
  constructor
  · -- Show 36 is in the set
    use 3
    constructor
    · -- Show n = ∑ i ∈ Finset.range 4, (2 * i + 2 * 3)
      norm_num [Finset.sum_range_succ]
    constructor
    · -- Show ∃ m, m ^ 2 = 36
      use 6
      all_goals norm_num
    · -- Show ∀ i ∈ Finset.range 4, 0 < (2 * i + 2 * 3)
      intro i hi
      fin_cases hi <;> norm_num
  · -- Show 36 is the least in the set
    intro n hn
    rcases hn with ⟨k, heq, ⟨m, hm⟩, hpos⟩
    have h1 : n = 8 * k + 12 := by
      norm_num [Finset.sum_range_succ] at heq
      linarith
    rw [h1] at hm
    by_contra h
    push_neg at h
    have h2 : m ^ 2 = 8 * k + 12 := hm
    have h3 : m ≤ 5 := by
      nlinarith
    have h6 : (m : ℤ) ^ 2 = 8 * (k : ℤ) + 12 := by
      have h7 : m ^ 2 = 8 * k + 12 := h2
      have h8 : (m : ℤ) ^ 2 = (8 * k + 12 : ℕ) := by exact_mod_cast h7
      norm_num at h8 ⊢
      all_goals 
        try { 
          omega 
        }
        <;> try { 
          nlinarith 
        }
    have h7 : (m : ℤ) ≤ 5 := by
      nlinarith [h6]
    have h8 : (m : ℤ) ≥ -5 := by
      nlinarith [h6]
    interval_cases (m : ℤ) <;> try { 
      omega 
      <;> try { 
        have : k < 3 := by 
          nlinarith 
        interval_cases k <;> try { 
          omega 
        } <;> try { 
          nlinarith 
        } 
      }
      <;> try { 
        tauto 
      }
    }
    all_goals
      try { 
        exfalso 
        <;> 
        try { 
          tauto 
        } 
        <;> try { 
          nlinarith 
        } 
        <;> try { 
          nlinarith 
        } 
      }
      <;> try { 
        nlinarith 
      }