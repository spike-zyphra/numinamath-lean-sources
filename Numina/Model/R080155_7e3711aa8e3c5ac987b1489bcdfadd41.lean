import Mathlib

theorem algebra_292329 (a : ℝ) (ha : a > 2) (a_seq : ℕ → ℝ)
    (h_a0 : a_seq 0 = 1) (h_a1 : a_seq 1 = a)
    (h_an : ∀ n, a_seq (n + 1) = ((a_seq n)^2 / (a_seq (n - 1))^2 - 2) * a_seq n) :
    ∀ k, ∑ i in Finset.Icc 0 k, (1 / a_seq i) < ((2 + a - Real.sqrt (a^2 - 4)) / 2) := by 
  have h1 := h_an 0
  norm_num [h_a0] at h1
  all_goals
    linarith [h_a1, h1, h_a0]