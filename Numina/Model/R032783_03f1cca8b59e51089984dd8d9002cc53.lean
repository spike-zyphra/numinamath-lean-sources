import Mathlib

theorem algebra_9933 {x : ℕ → ℝ} {a b : ℝ} (h : ∀ n ≥ 2, x (n + 1) = x n - x (n - 1)) (hx1 : x 1 = a) (hx2 : x 2 = b)
    (S : ℕ → ℝ) (hS : ∀ n, S n = ∑ i ∈ Finset.Icc 1 n, x i) :
    x 100 = -a ∧ S 100 = 2 * b - a := by
  constructor
  · -- Proof that x 100 = -a 
    norm_num [h, hx1, hx2]
    all_goals 
      linarith 
  · -- Proof that S 100 = 2 * b - a 
    rw [hS 100]
    norm_num [Finset.sum_Icc_succ_top, hx1, hx2, h]
    all_goals 
      linarith