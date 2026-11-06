import Mathlib

open Finset Real

lemma mul_le_sum_div_two (a b : ℝ) : a * b ≤ ((a + b) / 2) ^ 2:= by
  field_simp 
  nlinarith [sq_nonneg (a - b)]

theorem number_theory_638473 {n : ℕ} (hn : 1 < n) :
  ∏ i ∈ range n, (i + 1 : ℝ) < ((n + 1) / 2 : ℝ)^n := by 
  have h1 : (∏ i ∈ range n, (i + 1 : ℝ)) ^ 2 < 
    ∏ i ∈ range n, (((n + 1 )/ 2 : ℝ) ^ 2) := by 
    calc 
      _ = (∏ i ∈ range n, (i + 1 : ℝ)) * (∏ i ∈ range n, (i + 1 : ℝ))  := by 
        ring
      _ < _ := by 
        have aux : ∏ i ∈ range n, (i + 1 : ℝ) = ∏ i ∈ range n, (n - i : ℝ) := by 
          let t : ℕ → ℕ := fun x => n - 1 - x
          refine prod_nbij' t t ?_ ?_ ?_ ?_ ?_
          · simp 
            intro x hx
            unfold t
            omega
          · simp 
            intro x hx
            unfold t
            omega
          · simp 
            intro x hx
            unfold t
            omega
          · simp 
            intro x hx
            unfold t
            omega
          · simp 
            intro x hx
            unfold t 
            rw [Nat.cast_sub, Nat.cast_sub]
            ring
            linarith
            omega
        nth_rw 1 [aux] 
        rw [←prod_mul_distrib]
        refine prod_lt_prod ?_ ?_ ?_
        · intro i hi
          simp at hi
          have ge1 : (n : ℝ) - i > 0 := by 
            have ngti : (n : ℝ) > i := by 
              norm_cast
            linarith
          positivity
        · intro i hi
          simp at hi
          obtain h1 := mul_le_sum_div_two (n - i : ℝ) (i + 1 : ℝ)
          linarith
        · use 0
          constructor
          · simp
            linarith
          · simp
            field_simp
            refine (lt_div_iff₀ ?_).mpr ?_
            · linarith
            · ring_nf
              have ineq : (n : ℝ) ^ 2 + 1 > 2 * n := by 
                norm_cast
                have ineq_aux : n * n ≥ 2 * n := by 
                  apply mul_le_mul
                  all_goals linarith
                linarith
              linarith
  have h2 : ∏ i ∈ range n, (((n + 1 )/ 2 : ℝ) ^ 2) = (∏ i ∈ range n, ((n + 1 )/ 2 : ℝ) ) ^ 2 := by 
    exact prod_pow (range n) 2 fun x => ((n : ℝ) + 1) / 2
  have h3 : ∏ i ∈ range n, ((n + 1 )/ 2 : ℝ) = ((n + 1 )/ 2 : ℝ) ^ n := by
    exact Eq.symm (pow_eq_prod_const (((n : ℝ) + 1) / 2) n)
  have pos1 : ∏ i ∈ range n, (i + 1 : ℝ) ≥ 0 := by 
    apply prod_nonneg
    intro i hi
    norm_cast
    linarith
  have pos2 : ((n + 1) / 2 : ℝ)^n ≥ 0 := by 
    positivity
  rw [h2, h3] at h1
  exact (sq_lt_sq₀ pos1 pos2).mp h1