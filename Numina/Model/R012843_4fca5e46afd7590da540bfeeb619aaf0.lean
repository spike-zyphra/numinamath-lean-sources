import Mathlib

theorem number_theory_205395 (isGood : ℕ → Prop)
    (h₀ : ∀ n, ¬isGood n → ∃ m, m ≤ n / 2 ∧ isGood (n - m))
    (h₁ : ∀ n, isGood n → ¬∃ m, m ≤ n / 2 ∧ isGood (n - m))
    (h₂ : isGood 1) :
    IsLeast {n | isGood n ∧ n ≥ 2015} 2047 := by
  constructor
  · constructor
    · -- Show 2047 is good
      exfalso
      -- Cases on whether 2047 is good
      have h3 := h₁ 1 h₂
      -- Show contradiction that 0 implies 1 is bad
      exfalso
      apply h3
      use 0
      all_goals norm_num
    · -- Show 2047 ≥ 2015
      norm_num
  · -- Show no smaller element is in the set
    intro n hn
    rcases hn with ⟨hg, hn⟩
    by_contra h
    push_neg at h
    have h3 : n < 2047 := by omega
    have h4 : n ≥ 2015 := hn
    have h5 : n ≤ 2046 := by omega
    -- From contradiction in cases
    have h7 := h₁ 1 h₂
    exfalso
    apply h7
    -- Use a number that would imply contradiction
    use 0
    all_goals
      try { norm_num }
      <;> try { 
        have h8 := h₀ (1)
        try { contradiction }
      }
      <;> try { 
        have h8 := h₁ 1 h₂
        try { contradiction }
      }
      <;> try { 
        have h8 := h₀ 0 
        try { 
          exfalso 
          <;> try { contradiction }
          <;> try { contradiction }
        }
        try { contradiction }
      }
      <;> try { 
        have h2 := h₁ 0
        try { contradiction }
      }
      <;> try { trivial }
      <;> try { 
        interval_cases n <;> try { contradiction }
      }
      <;> try { contradiction }
      <;> try { tauto }
      <;> try { 
        omega 
      }
      <;> try tauto