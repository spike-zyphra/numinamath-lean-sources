import Mathlib

theorem number_theory_184871 (k : ℕ) :
    IsSquare (4 * k + 5) ∧ IsSquare (9 * k + 4) ↔ 7 * k + 4 = 39 := by
  constructor
  · -- Assume both expressions are squares, prove 7*k + 4 = 39
    rintro ⟨h₁, h₂⟩
    rcases h₁ with ⟨a, ha⟩
    rcases h₂ with ⟨b, hb⟩
    by_cases h : a ≤ 30
    · -- a ≤ 30
      have h4 : b ≤ 90 := by nlinarith [ha, hb]
      interval_cases a <;> try { 
        omega
      } <;> try { 
        interval_cases b <;> omega
      }
    · -- a > 30
      have h30 : a > 30 := by 
        omega
      have eq1 : 9 * a ^ 2 = 4 * b ^ 2 + 29 := by 
        nlinarith [ha, hb]
      have eq2 : (3 * a : ℤ) ^ 2 - (2 * b : ℤ) ^ 2 = 29 := by
        nlinarith [eq1]
      have h1 : (3 * a : ℤ) ^ 2 - (2 * b : ℤ) ^ 2 = 29 := eq2
      have h2 : (3 * a - 2 * b : ℤ) * (3 * a + 2 * b : ℤ) = 29 := by 
        nlinarith [eq2]
      have h3 : (3 * a - 2 * b : ℤ) ∣ 29 := by 
        use (3 * a + 2 * b : ℤ)
        all_goals linarith
      have h4 : (3 * a - 2 * b : ℤ) ≤ 29 := by 
        have h5 : (3 * a - 2 * b : ℤ) ∣ 29 := h3
        have h6 : (3 * a - 2 * b : ℤ) ≤ 29 := by 
          have h7 : (3 * a - 2 * b : ℤ) ∣ 29 := h3
          have h8 : (3 * a - 2 * b : ℤ) ≤ 29 := by 
            exact Int.le_of_dvd (by norm_num) h7
          linarith
        linarith
      have h5 : (3 * a - 2 * b : ℤ) ≥ -29 := by
        have h5 : (3 * a - 2 * b : ℤ) ∣ 29 := h3
        have h6 : (3 * a - 2 * b : ℤ) ≥ -29 := by 
          have h7 : (3 * a - 2 * b : ℤ) ∣ 29 := h3
          have h8 : -( (3 * a - 2 * b : ℤ) ) ∣ 29 := by 
            exact Int.neg_dvd.2 h7
          have h9 : -( (3 * a - 2 * b : ℤ) ) ≤ 29 := by 
            exact Int.le_of_dvd (by norm_num) h8
          omega
        linarith
      interval_cases h6 : (3 * a - 2 * b : ℤ) <;> try { 
        omega
      } <;> try { 
        all_goals
        try { 
          exfalso 
          <;> try { 
            nlinarith [sq_nonneg ((a: ℤ) - 5), sq_nonneg ((b: ℤ) - 7), sq_nonneg (a * (a - 5)), sq_nonneg (b * (b - 7))]
          }
        }
      }
  · -- Assume 7*k+4=39, prove both expressions are squares
    intro h
    have hk : k = 5 := by 
      omega
    constructor
    · -- 4 * k + 5 is a square
      rw [hk]
      native_decide
    · -- 9 * k + 4 is a square
      rw [hk]
      native_decide