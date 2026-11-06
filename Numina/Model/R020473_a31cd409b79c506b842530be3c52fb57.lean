import Mathlib

theorem algebra_10913 {P : ℕ → ℝ} (hP : ∀ n, P n = if n ≤ 5 then (1 / 2) ^ n * P 0 else 0)
    (hP0 : P 0 + ∑ n in Finset.Icc 1 5, P n = 1) :
    P 0 = 32 / 63 := by
  have eq1 : P 1 = (1 / 2 : ℝ) * P 0 := by
    specialize hP 1
    norm_num [if_pos] at hP ⊢
    linarith
  have eq2 : P 2 = (1 / 4 : ℝ) * P 0 := by
    specialize hP 2
    norm_num [if_pos] at hP ⊢
    linarith
  have eq3 : P 3 = (1 / 8 : ℝ) * P 0 := by
    specialize hP 3
    norm_num [if_pos] at hP ⊢
    linarith
  have eq4 : P 4 = (1 / 16 : ℝ) * P 0 := by
    specialize hP 4
    norm_num [if_pos] at hP ⊢
    linarith
  have eq5 : P 5 = (1 / 32 : ℝ) * P 0 := by
    specialize hP 5
    norm_num [if_pos] at hP ⊢
    linarith
  have eq6 : ∑ n in Finset.Icc 1 5, P n = (1 / 2 : ℝ) * P 0 + (1 / 4 : ℝ) * P 0 + (1 / 8 : ℝ) * P 0 + (1 / 16 : ℝ) * P 0 + (1 / 32 : ℝ) * P 0 := by
    simp [Finset.sum_Icc_succ_top, eq1, eq2, eq3, eq4, eq5]
    <;> ring
  rw [eq6] at hP0
  linarith