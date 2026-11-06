import Mathlib

open Finset Real

theorem algebra_191841 {n : ℕ} :
    ∑ i ∈ range n, (1 / ((3 * i + 2) * (3 * i + 5))) = n / (2 * (3 * n + 2)) := by

  have h1 : ∀ (n : ℕ), ∑ i ∈ range n, (1 / ((3 * i + 2) * (3 * i + 5))) = n / (2 * (3 * n + 2)) := by
    intro n
    induction n with 
    | zero => 
      simp 
    | succ n ih => 
      rw [sum_range_succ, ih]
      have eq1 : n / (2 * (3 * n + 2)) + 1 / ((3 * n + 2) * (3 * n + 5)) = (n + 1) / (2 * (3 * (n + 1) + 2)) := by 
        have eq2 : n / (2 * (3 * n + 2)) + 1 / ((3 * n + 2) * (3 * n + 5)) = 0 := by 
          have h2 : 1 / ((3 * n + 2) * (3 * n + 5)) = 0 := by
            have h3 : (3 * n + 2) * (3 * n + 5) > 1 := by
              nlinarith 
            have : 1 / ((3 * n + 2) * (3 * n + 5)) = 0 := by 
              rw [Nat.div_eq_zero_iff]
              omega 
            assumption
          have h4 : n / (2 * (3 * n + 2)) = 0 := by
            have : n < 2 * (3 * n + 2) := by
              nlinarith 
            apply Nat.div_eq_zero_iff.mpr 
            omega 
          rw [h2, h4]
          all_goals omega 
        have eq3 : (n + 1) / (2 * (3 * (n + 1) + 2)) = 0 := by
          have h5 : (n + 1) / (2 * (3 * (n + 1) + 2)) = 0 := by
            have h6 : 2 * (3 * (n + 1) + 2) > (n + 1) := by
              nlinarith [sq_nonneg (n : ℕ)]
            apply Nat.div_eq_zero_iff.mpr 
            omega 
          assumption 
        rw [eq2, eq3]
      exact eq1 
  specialize h1 n 
  simpa using h1