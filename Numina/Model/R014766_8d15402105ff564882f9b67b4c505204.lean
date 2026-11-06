import Mathlib

theorem algebra_34920 {n : ℕ} (hn : 0 < n) (a : ℕ → ℝ)
    (ha : ∀ j ∈ Finset.Icc 1 n, a j ≠ 1) :
    a 1 + ∑ i ∈ Finset.Icc 2 n, a i * ∏ j ∈ Finset.Icc 1 (i - 1), (1 - a j) =
    1 - ∏ j ∈ Finset.Icc 1 n, (1 - a j) := by
  have h1 : ∀ k : ℕ, k ≥ 1 →
    a 1 + ∑ i ∈ Finset.Icc 2 k, a i * ∏ j ∈ Finset.Icc 1 (i - 1), (1 - a j) =
    1 - ∏ j ∈ Finset.Icc 1 k, (1 - a j) := by
    intro k hk
    induction k with 
    | zero => 
      exfalso
      omega
    | succ k ih =>
      cases k with
      | zero => 
        simp at *
        <;> norm_num at ih ⊢ 
        all_goals try { 
          tauto
        }
      | succ k => 
        simp [Finset.sum_Icc_succ_top, Finset.prod_Icc_succ_top] at ih ⊢
        <;> ring_nf at ih ⊢ 
        <;> try { 
          nlinarith [sq_nonneg (a 1 - 1), sq_nonneg (a 2 - 1), sq_nonneg (a (k + 1) - 1), sq_nonneg (a (k + 2) - 1), sq_nonneg ((1 - a 1) ), sq_nonneg ((1 - a 2) ), sq_nonneg ((1 - a (k + 1)) ), sq_nonneg ((1 - a (k + 2)) ), mul_self_nonneg (a 1), mul_self_nonneg (a 2), mul_self_nonneg (a (k + 1)), mul_self_nonneg (a (k + 2))]
        }
  have h2 := h1 n (by omega)
  simpa using h2