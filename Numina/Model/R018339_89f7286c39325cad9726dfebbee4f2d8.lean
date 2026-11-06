import Mathlib

theorem number_theory_294613 (q : ℕ → ℕ) (hq : ∀ i, q i = (q (i - 1) - 1)^3 + 3)
    (hpos : q 0 > 0) (hprime : ∀ i, ∃ p k, Nat.Prime p ∧ q i = p^k) :
    IsGreatest {n | ∀ i ∈ Finset.Icc 1 n, ∃ p k, Nat.Prime p ∧ q i = p^k} 2 := by 
  have h0 := hq 0
  simp at h0 
  all_goals
    exfalso
    have h1 : q 0 > 0 := hpos 
    have h6 : q 0 = (q 0 - 1)^3 + 3 := by
      omega 
    have h7 : q 0 = (q 0 - 1)^3 + 3 := by
      linarith 
    have h8 : q 0 ≥ 1 := by 
      omega 
    have h9 : q 0 ≥ 1 := by
      omega 
    -- Let's analyze.
    -- We need to show contradiction in h7.
    -- We have q 0 = (q 0 - 1)^3 + 3 and q 0 > 0.
    -- Let's replace.
    -- Let's check small cases.
    -- q 0 = 1: 1 = 0 + 3 = 3
    -- q 0 = 2: 2 = 1 + 3 = 4
    -- So as we can see, RHS is larger.
    -- Hence impossible
    have h10 : q 0 < q 0 := by
      by_cases h : q 0 ≤ 1 
      · -- Case q 0 = 1
        have hq1 : q 0 = 1 := by linarith 
        rw [hq1] at h7 
        norm_num at h7 
        all_goals 
          linarith 
      · 
        have hq0 : q 0 ≥ 2 := by 
          omega 
        have h3 : q 0 < (q 0 - 1)^3 + 3 := by
          have h5 : q 0 - 1 ≥ 1 := by 
            omega 
          -- induction
          have h4 : (q 0 - 1)^3 + 3 > q 0 := by
            have h5 : q 0 ≥ 2 := by linarith 
            have h6 : q 0 - 1 ≥ 1 := by linarith 
            have h7 : ((q 0 - 1) : ℕ) ^ 3 ≥ (q 0 - 1) := by
              have h8 : (q 0 - 1) ≥ 1 := by linarith 
              have h9 : ((q 0 - 1) : ℕ) ^ 3 ≥ (q 0 - 1) := by
                have : (q 0 - 1 : ℕ) ^ 3 ≥ (q 0 - 1 : ℕ) := by
                  nlinarith [sq_nonneg ((q 0 - 1 : ℕ) - 1), sq_nonneg ((q 0 - 1 : ℕ)), h8]
                linarith 
              linarith 
            have h10 : ((q 0 - 1) : ℕ) ^ 3 + 3 > (q 0 - 1) + 0 := by 
              omega 
            omega 
          linarith 
        linarith [h7, h3] 
    linarith 
    all_goals 
      exfalso
      <;> try linarith 
      <;> norm_num 
      <;> try tauto
      <;> try tauto 
      <;> try linarith 
      <;> try linarith