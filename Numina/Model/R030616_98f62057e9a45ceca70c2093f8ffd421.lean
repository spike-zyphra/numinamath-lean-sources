import Mathlib

open Set Real

theorem inequalities_307132 (M N : Set ℝ) (hM : M = {x | abs (3 - x) / abs (5 - x) ≤ 1 / 2})
    (hN : N = {x | x ^ 2 - 2 * x + c ≤ 0}) (hc : ∀ x ∈ M, x ∈ N) :
    c ≤ -55 / 9 := by
  have h1 : (11 / 3 : ℝ) ∈ M := by
    rw [hM]
    dsimp
    have h2 : abs (3 - (11 / 3 : ℝ)) = (2 / 3 : ℝ) := by
      norm_num [abs_of_nonneg, abs_of_nonpos]
      all_goals norm_num
    have h3 : abs (5 - (11 / 3 : ℝ)) = (4 / 3 : ℝ) := by
      norm_num [abs_of_nonneg, abs_of_nonpos]
      all_goals norm_num
    rw [h2, h3]
    norm_num
    all_goals norm_num
  have h4 : (11 / 3 : ℝ) ∈ N := by
    apply hc
    exact h1
  rw [hN] at h4
  dsimp at h4
  norm_num at h4 ⊢
  linarith