import Mathlib

theorem algebra_239516 {a : ℝ} (ha : a > 2) (a_seq : ℕ → ℝ)
    (h_a0 : a_seq 0 = 1) (h_a1 : a_seq 1 = a)
    (h_an : ∀ n, a_seq (n + 1) = ((a_seq n)^2 / (a_seq (n - 1))^2 - 2) * a_seq n) :
    ∀ k, ∑ i in Finset.Icc 0 k, (1 / a_seq i) < ((2 + a - Real.sqrt (a^2 - 4)) / 2) := by 
  have h₁ := h_an 0
  simp [Nat.succ_eq_add_one, h_a0] at h₁
  all_goals 
    linarith [Real.sqrt_nonneg (a ^ 2 - 4), Real.sq_sqrt (show (a ^ 2 - 4) ≥ 0 by nlinarith), sq_nonneg (a - Real.sqrt (a^2 - 4))]