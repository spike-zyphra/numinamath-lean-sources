import Mathlib

open Real

theorem inequalities_113917 (a : ℕ → ℝ) (r : ℝ) (h : ∀ n, a n = a 0 + r * (n - 1)) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range (2 * n), |a (i + 1)| ≥ n * |r| := by
  have h0 := h 0
  norm_num at h0
  by_cases hr : r = 0
  · -- Case r = 0
    have h1 : ∀ (i : ℕ), a (i + 1) = a 0 := by 
      intro i
      specialize h (i + 1)
      simp [hr] at h ⊢
      linarith 
    have h2 : ∑ i in Finset.range (2 * n), |a (i + 1)| = (2 * n) * |a 0| := by
      simp_rw [h1]
      simp [Finset.sum_const, mul_comm]
    rw [h2, hr]
    all_goals 
      norm_num 
    all_goals 
      nlinarith [abs_nonneg (a 0)]
  · -- Case r ≠ 0
    exfalso
    apply hr
    linarith [abs_nonneg r, h0]