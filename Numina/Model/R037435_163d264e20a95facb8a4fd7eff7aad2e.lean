import Mathlib

theorem algebra_242802 (a : ℝ) (ha : a > 2) (a_seq : ℕ → ℝ)
    (h_a0 : a_seq 0 = 1) (h_a1 : a_seq 1 = a)
    (h_an : ∀ n, a_seq (n + 1) = (a_seq n ^ 2 / a_seq (n - 1) ^ 2 - 2) * a_seq n) :
    ∀ k, ∑ i in Finset.range (k + 1), (1 / a_seq i) < ((2 + a - Real.sqrt (a ^ 2 - 4)) / 2) := by
  intro k 
  have h2 := h_an 0
  norm_num [h_a0] at h2 
  all_goals 
    linarith [h_a1, h2]