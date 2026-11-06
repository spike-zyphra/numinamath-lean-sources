import Mathlib
theorem number_theory_115474 {a b c : ℝ} (ha : 0 ≤ a ∧ a < 1) 
    (hb : 0 ≤ b ∧ b < 1) (hc : 0 ≤ c ∧ c < 1) (hh : a ≠ b ∧ a ≠ c ∧ b ≠ c): 
    ∃ (x y : ℝ) ,x ∈ ({a, b, c} : Set ℝ) ∧ y ∈ ({a, b, c} : Set ℝ)∧ x ≠ y ∧ |y - x| < 1/2 := by
  have ha1 : 0 ≤ a := ha.1
  have ha2 : a < 1 := ha.2
  have hb1 : 0 ≤ b := hb.1
  have hb2 : b < 1 := hb.2
  have hc1 : 0 ≤ c := hc.1
  have hc2 : c < 1 := hc.2
  by_cases h1 : a < 1/2
  · -- Case 1: a < 1/2
    by_cases h2 : b < 1/2
    · -- Case 1.1: a < 1/2 and b < 1/2
      use a, b 
      constructor
      · -- Show a ∈ {a,b,c}
        simp
      constructor
      · -- Show b ∈ {a,b,c}
        simp
      constructor
      · -- Show a ≠ b 
        exact hh.1
      · -- Show |b - a| < 1/2 
        rw [abs_lt]
        constructor
        · -- Show -(1/2) < b - a
          linarith
        · -- Show b - a < 1/2
          linarith
    · -- Case 1.2: a < 1/2 and b ≥ 1/2 
      by_cases h3 : c < 1/2 
      · -- Case 1.2.1: a < 1/2 and c < 1/2 
        use a, c 
        constructor
        · -- Show a ∈ {a,b,c}
          simp
        constructor
        · -- Show c ∈ {a,b,c}
          simp
        constructor
        · -- Show a ≠ c
          exact hh.2.1
        · -- Show |c - a| < 1/2 
          rw [abs_lt]
          constructor
          · -- Show -(1/2) < c - a
            linarith
          · -- Show c - a < 1/2
            linarith
      · -- Case 1.2.2: a < 1/2 and c ≥ 1/2 
        -- Then b and c are both in [1/2, 1)
        use b, c 
        constructor
        · -- Show b ∈ {a,b,c}
          simp
        constructor
        · -- Show c ∈ {a,b,c}
          simp
        constructor
        · -- Show b ≠ c
          exact hh.2.2
        · -- Show |c - b| < 1/2 
          rw [abs_lt]
          constructor
          · -- Show -(1/2) < c - b
            linarith
          · -- Show c - b < 1/2 
            linarith
  · -- Case 2: a ≥ 1/2
    by_cases h2 : b < 1/2
    · -- Case 2.1: a ≥ 1/2 and b < 1/2 
      by_cases h3 : c < 1/2 
      · -- Case 2.1.1: a ≥ 1/2 and c < 1/2 
        -- Then a and c are both in [0,1/2) or [1/2,1) 
        -- Wait, actually a >= 1/2 and c < 1/2.
        -- So take b and c or a and b.
        -- Wait, b < 1/2 and c < 1/2
        -- So b and c are both in [0, 1/2)
        use b, c 
        constructor
        · -- Show b ∈ {a,b,c}
          simp
        constructor
        · -- Show c ∈ {a,b,c}
          simp
        constructor
        · -- Show b ≠ c
          exact hh.2.2
        · -- Show |c - b| < 1/2 
          rw [abs_lt]
          constructor
          · -- Show -(1/2) < c - b
            linarith
          · -- Show c - b < 1/2 
            linarith
      · -- Case 2.1.2: a ≥ 1/2 and c ≥ 1/2 
        -- Then a and c are both in [1/2, 1)
        use a, c 
        constructor
        · -- Show a ∈ {a,b,c}
          simp
        constructor
        · -- Show c ∈ {a,b,c}
          simp
        constructor
        · -- Show a ≠ c
          exact hh.2.1
        · -- Show |c - a| < 1/2 
          rw [abs_lt]
          constructor
          · -- Show -(1/2) < c - a
            linarith
          · -- Show c - a < 1/2 
            linarith
    · -- Case 2.2: a ≥ 1/2 and b ≥ 1/2 
      by_cases h3 : c < 1/2 
      · -- Case 2.2.1: a ≥ 1/2 and c < 1/2 
        -- Then a and b are both in [1/2,1)
        use a, b 
        constructor
        · -- Show a ∈ {a,b,c}
          simp
        constructor
        · -- Show b ∈ {a,b,c}
          simp
        constructor
        · -- Show a ≠ b
          exact hh.1
        · -- Show |b - a| < 1/2 
          rw [abs_lt]
          constructor
          · -- Show -(1/2) < b - a
            linarith
          · -- Show b - a < 1/2 
            linarith
      · -- Case 2.2.2: a ≥ 1/2 and c ≥ 1/2 
        -- Then a and c are both in [1/2,1)
        use a, c 
        constructor
        · -- Show a ∈ {a,b,c}
          simp
        constructor
        · -- Show c ∈ {a,b,c}
          simp
        constructor
        · -- Show a ≠ c
          exact hh.2.1
        · -- Show |c - a| < 1/2 
          rw [abs_lt]
          constructor
          · -- Show -(1/2) < c - a
            linarith
          · -- Show c - a < 1/2 
            linarith