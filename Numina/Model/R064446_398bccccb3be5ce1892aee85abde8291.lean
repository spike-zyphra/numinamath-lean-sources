import Mathlib

theorem algebra_305313 {a : ℕ → ℝ} (ha : ∀ n, ∑ i in Finset.Icc 1 n, a i = n ^ 3) :
    ∑ i in Finset.Icc 2 100, (1 / (a i - 1)) = 33 / 100 := by

  have ha1 : ∀ n, a (n + 1) = 3 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 1 := by
    intro n
    have h1 := ha (n + 1)
    have h2 := ha n
    rw [Finset.sum_Icc_succ_top (by linarith)] at h1
    simp [Finset.sum_Icc_succ_top] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    linarith

  norm_num [Finset.sum_Icc_succ_top, ha1] at *
  <;> try { norm_num }
  <;> try { linarith }