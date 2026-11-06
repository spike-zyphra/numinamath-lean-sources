import Mathlib

open Finset Real

theorem inequalities_300633 (n : ℕ) (hn : 0 < n) :
    ∏ i ∈ range n, (1 - 1 / 3 ^ (i + 1)) > 1 / 2 := by

  have h3 : ∀ (n : ℕ), ∏ i ∈ range n, (1 - 1 / 3 ^ (i + 1) ) > 1 / 2 := by
    intro n
    induction n with 
    | zero =>
      simp 
    | succ n ih =>
      rw [prod_range_succ]
      norm_num at ih ⊢ 
      all_goals 
        try { 
          nlinarith [ sq_nonneg ( ( ∏ i ∈ range n, (1 - 1 / 3 ^ (i + 1) ) ) - (1 : ℚ ) / 2 ), sq_nonneg ( (1 - (1 : ℚ ) / 3 ^ (n + 1) ) - 2 / 3 ) ]
        }
        all_goals
          try { 
            norm_num at ih ⊢ 
          }
  specialize h3 n
  simpa using h3