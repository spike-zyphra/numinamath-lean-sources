import Mathlib

theorem algebra_108090 (n : ℕ) (h : √(n * 17^2) = 17^2 + 17^2 + 17^2) :
    n = 2601 := by
  have h1 : (n * 17 ^ 2 : ℝ) ≥ 0 := by
    positivity
  have h2 : (√(n * 17 ^ 2) : ℝ) ^ 2 = (17 ^ 2 + 17 ^ 2 + 17 ^ 2 : ℝ) ^ 2 := by
    rw [h]
  have h3 : (√(n * 17 ^ 2) : ℝ) ^ 2 = (n * 17 ^ 2 : ℝ) := Real.sq_sqrt (by
    positivity
  )
  rw [h3] at h2
  have h4 : (17 ^ 2 + 17 ^ 2 + 17 ^ 2 : ℝ) ^ 2 = (9 * (17 ^ 2 : ℝ) ^ 2) := by
    ring_nf
  rw [h4] at h2
  have h5 : (n * 17 ^ 2 : ℝ) = (9 * (17 ^ 2 : ℝ) ^ 2) := by
    nlinarith
    <;> norm_num at h2 ⊢
  have h6 : (n : ℝ) = 2601 := by
    norm_num at h5 ⊢
    nlinarith
    all_goals nlinarith
    <;> norm_num at h5 ⊢
    all_goals nlinarith
  exact_mod_cast h6