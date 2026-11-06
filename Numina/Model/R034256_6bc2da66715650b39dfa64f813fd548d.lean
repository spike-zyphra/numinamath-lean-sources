import Mathlib

theorem algebra_3310 (n : ℕ) (hn : 0 < n) :
    (∑ i in Finset.Icc 1 n, i^2) / (∑ i in Finset.Icc 1 n, i * (i + 1)) - 3 ≤ 0 := by
  have h1 : ∀ n : ℕ, 0 < n → ∑ i in Finset.Icc 1 n, i ^ 2 ≤ 3 * (∑ i in Finset.Icc 1 n, i * (i + 1)) := by
    intro n hn
    induction n with
    | zero => 
      exfalso 
      linarith 
    | succ n ih => 
      cases n with 
      | zero => 
        simp at ih ⊢ 
      | succ n => 
        simp [Finset.sum_Icc_succ_top, mul_add, add_mul, pow_two] at ih ⊢ 
        all_goals 
          ring_nf at ih ⊢ 
          omega 
  have h2 : (∑ i in Finset.Icc 1 n, i^2) ≤ 3 * (∑ i in Finset.Icc 1 n, i * (i + 1)) := h1 n hn
  have h3 : (∑ i in Finset.Icc 1 n, i^2) / (∑ i in Finset.Icc 1 n, i * (i + 1)) ≤ 3 := by 
    apply Nat.div_le_of_le_mul 
    linarith [h2] 
  omega