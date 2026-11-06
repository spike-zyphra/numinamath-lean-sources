import Mathlib

open Real

theorem number_theory_116947 :
    ∃c d : ℤ, c ≠ 0 ∧ d ≠ 0 ∧ 
      ∃ n : ℕ, ∃ r : Fin n → ℝ, 
        (∀ i, ∃a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ r i = sqrt (a + b * sqrt 2)) ∧ 
        sqrt (c + d * sqrt 7) = ∑ i, r i 
  := by
  use 6, 2
  constructor
  · -- Show c ≠ 0
    norm_num
  constructor
  · -- Show d ≠ 0
    norm_num
  use 2
  use λ i =>
    match i with
    | 0 => Real.sqrt (3 + Real.sqrt 2)
    | 1 => Real.sqrt (3 - Real.sqrt 2)
    | _ => (0 : ℝ)
  constructor
  · -- Show all r i are square roots of integer combinations of sqrt 2
    intro i
    fin_cases i <;> 
      try { 
        use 3, 1 
        all_goals 
          try { 
            norm_num 
          } 
          <;> try { 
            simp 
          } 
      } <;> 
      try { 
        use 3, -1 
        all_goals 
          try { 
            norm_num 
          } 
          <;> try { 
            have h1 : Real.sqrt (3 - Real.sqrt 2) = Real.sqrt (3 + (-1 : ℤ) * Real.sqrt 2) := by
              ring_nf
            simp [h1] 
          } 
      }
  · -- Show sqrt (6 + 2 * sqrt 7) = r 0 + r 1
    have h2 : Real.sqrt ((6 : ℝ) + (2 : ℝ) * Real.sqrt 7) = Real.sqrt (3 + Real.sqrt 2) + Real.sqrt (3 - Real.sqrt 2) := by
      have h3 : (Real.sqrt (3 + Real.sqrt 2) + Real.sqrt (3 - Real.sqrt 2)) ^ 2 = (6 : ℝ) + (2 : ℝ) * Real.sqrt 7 := by
        have h4 : 0 ≤ (3 - Real.sqrt 2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        have h5 : Real.sqrt (3 + Real.sqrt 2) ^ 2 = 3 + Real.sqrt 2 := by
          rw [Real.sq_sqrt]
          positivity
        have h6 : Real.sqrt (3 - Real.sqrt 2) ^ 2 = 3 - Real.sqrt 2 := by
          rw [Real.sq_sqrt]
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        have h7 : Real.sqrt (3 + Real.sqrt 2) * Real.sqrt (3 - Real.sqrt 2) = Real.sqrt 7 := by
          have h8 : Real.sqrt (3 + Real.sqrt 2) * Real.sqrt (3 - Real.sqrt 2) = Real.sqrt ((3 + Real.sqrt 2) * (3 - Real.sqrt 2)) := by 
            rw [← Real.sqrt_mul (by
              have h4 : 0 ≤ (3 + Real.sqrt 2 : ℝ) := by positivity
              have h5 : 0 ≤ (3 - Real.sqrt 2 : ℝ) := by
                nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
              all_goals nlinarith
            )
            ]
          have h9 : (3 + Real.sqrt 2) * (3 - Real.sqrt 2) = (7 : ℝ) := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          rw [h9] at h8
          linarith
        calc
          (Real.sqrt (3 + Real.sqrt 2) + Real.sqrt (3 - Real.sqrt 2)) ^ 2
              = Real.sqrt (3 + Real.sqrt 2) ^ 2 + Real.sqrt (3 - Real.sqrt 2) ^ 2 + 2 * (Real.sqrt (3 + Real.sqrt 2) * Real.sqrt (3 - Real.sqrt 2)) := by ring
          _ = (3 + Real.sqrt 2) + (3 - Real.sqrt 2) + 2 * (Real.sqrt (3 + Real.sqrt 2) * Real.sqrt (3 - Real.sqrt 2)) := by
            rw [h5, h6]
          _ = (3 + Real.sqrt 2) + (3 - Real.sqrt 2) + 2 * (Real.sqrt 7) := by
            rw [h7]
          _ = (6 : ℝ) + (2 : ℝ) * Real.sqrt 7 := by
            ring
      have h8 : Real.sqrt ((6 : ℝ) + (2 : ℝ) * Real.sqrt 7) ≥ 0 := Real.sqrt_nonneg _
      have h9 : Real.sqrt (3 + Real.sqrt 2) + Real.sqrt (3 - Real.sqrt 2) ≥ 0 := by positivity
      have h10 : (Real.sqrt ((6 : ℝ) + (2 : ℝ) * Real.sqrt 7)) ^ 2 = (Real.sqrt (3 + Real.sqrt 2) + Real.sqrt (3 - Real.sqrt 2)) ^ 2 := by
        rw [h3]
        all_goals
          rw [Real.sq_sqrt]
          positivity
      nlinarith [Real.sqrt_nonneg ((6 : ℝ) + (2 : ℝ) * Real.sqrt 7), Real.sqrt_nonneg (3 + Real.sqrt 2), Real.sqrt_nonneg (3 - Real.sqrt 2)]
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, h2]