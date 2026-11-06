import Mathlib

open Finset

theorem inequalities_232646 {n : ℕ} (hn : 1 < n) :
    ∏ i ∈ Icc 1 n, i ^ i < n ^ (n * (n + 1) / 2) := by
  have h₁ : n ^ (n * (n + 1) / 2) = ∏ i ∈ Icc 1 n, n ^ i := by 
    have h₂ : ∏ i in Icc 1 n, n ^ i = n ^ (∑ i in Icc 1 n, i) := by 
      rw [Finset.prod_pow_eq_pow_sum]
    -- Verify the implicit statement that n * (n - 1) / 2 is the sum
    have h45 : ∑ i in Icc 1 n, i = n * (n + 1) / 2 := by
      have h45 : ∀ (n : ℕ), ∑ i in Icc 1 n, i = n * (n + 1) / 2 := by
        intro n
        induction n with 
        | zero => 
          simp 
        | succ n ih => 
          rw [sum_Icc_succ_top (by linarith)]
          simp [ih]
          <;> ring_nf <;> omega 
      specialize h45 n 
      simpa using h45 
    rw [h₂] 
    rw [h45]
  rw [h₁]
  have h₂ : ∏ i ∈ Icc 1 n, i ^ i < ∏ i ∈ Icc 1 n, n ^ i := by
    apply Finset.prod_lt_prod
    · -- Show that all the terms of the second product are positive
      intro i hi
      have h10 : 1 ≤ i := by
        have h11 : i ∈ Icc 1 n := by
          exact hi
        simp at h11 ⊢ 
        omega 
      have h10_pos : i ^ i > 0 := by
        have h11 : i ≥ 1 := h10 
        have h14 : i ^ i ≥ 1 := by 
          have h12 : i ^ i ≥ 1 ^ i := by 
            apply Nat.pow_le_pow_of_le_left 
            all_goals 
              omega 
          have h14 : 1 ^ i = 1 := by 
            exact Nat.one_pow i 
          have h14' : 1 ^ i = 1 := h14 
          linarith [h14', h12] 
        omega 
      linarith 
    · -- Show that all the terms satisfy the inequality 
      intro i hi
      have h1 : i ^ i ≤ n ^ i := by 
        have h10 : 1 ≤ i := by 
          have h11 : i ∈ Icc 1 n := by 
            exact hi 
          simp at h11 ⊢ 
          omega 
        have h4 : i ≤ n := by 
          have h11 : i ∈ Icc 1 n := by 
            exact hi 
          simp at h11 ⊢ 
          omega 
        have h6 : i ≤ n := h4 
        have h11 : i ^ i ≤ n ^ i := by 
          apply Nat.pow_le_pow_of_le_left 
          all_goals 
            omega 
        omega 
      linarith 
    · -- Show that there exists an index where strict inequality holds 
      use 1 
      constructor 
      · -- Show that 1 is in the interval 
        have hx : 1 ∈ Icc 1 n := by
          simp at *
          all_goals 
            omega 
        exact hx 
      · -- Show that 1^1 < n^1 
        have h801 : 1 ^ 1 < n ^ 1 := by 
          apply Nat.pow_lt_pow_left 
          all_goals 
            omega 
        linarith 
  linarith