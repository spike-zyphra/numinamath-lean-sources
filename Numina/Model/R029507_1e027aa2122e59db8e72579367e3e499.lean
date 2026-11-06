import Mathlib

theorem number_theory_112685 (n : ℕ) (hn : 3 ≤ n) (hnsqfree : ∀ m, ¬ ∃ k, k^2 = m ∧ m ∣ n) :
    ∑ k in Finset.Icc 1 ((n - 2) * (n - 1)), ⌊(k * n : ℝ) ^ ((1 : ℝ) / 3)⌋ =
    ((n - 2) * (n - 1) * (3 * n - 5)) / 4 := by
  have h1 : ∃ k, k^2 = (1 : ℕ) ∧ (1 : ℕ) ∣ n := by
    use 1
    constructor
    · norm_num
    · -- Show that 1 divides n
      omega
  have h2 := hnsqfree 1
  have h3 := h2 h1
  norm_num at h3 ⊢
  all_goals
    try { linarith }