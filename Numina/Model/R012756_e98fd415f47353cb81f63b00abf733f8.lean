import Mathlib

theorem number_theory_129156 (y : ℕ) :
    IsSquare (y^2 + 5 * y + 12) ↔ y = 3 := by
  constructor
  · -- Assume $IsSquare (y^2 + 5 * y + 12)$, prove $y = 3$.
    rintro h
    rcases h with ⟨k, hk⟩
    by_cases h1 : y ≤ 3
    · -- y ≤ 3
      interval_cases y <;> try { 
        all_goals
          { 
            try { 
              have : k ≤ 7 := by nlinarith
              interval_cases k <;> try { omega }
            }
          }
        all_goals
          try { tauto }
          all_goals nlinarith
      }
    · -- y > 3
      have h2 : y > 3 := by omega
      have h3 : k > y := by
        nlinarith [sq_nonneg (k : ℕ), sq_nonneg (y : ℕ), hk]
      have h4 : k ≤ y + 2 := by
        by_contra h
        push_neg at h
        have h5 : k ≥ y + 3 := by
          omega
        have h6 : k ^ 2 ≥ (y + 3) ^ 2 := by nlinarith [h5, sq_nonneg (k : ℕ), sq_nonneg ((y + 3 : ℕ) : ℕ)]
        nlinarith [sq_nonneg (y : ℕ), sq_nonneg (k : ℕ), sq_nonneg ((y + 3 : ℕ) : ℕ), hk, h2]
      have h5 : k = y + 1 ∨ k = y + 2 := by
        omega
      rcases h5 with (h5 | h5)
      · -- k = y + 1
        rw [h5] at hk
        nlinarith [sq_nonneg (y : ℕ), sq_nonneg ((y + 1 : ℕ) : ℕ)]
      · -- k = y + 2
        rw [h5] at hk
        nlinarith [sq_nonneg (y : ℕ), sq_nonneg ((y + 2 : ℕ) : ℕ)]
  · -- Proof of the reverse direction: y = 3 → IsSquare (y^2 + 5 * y + 12)
    intro h
    rw [h]
    use 6
    all_goals
      norm_num