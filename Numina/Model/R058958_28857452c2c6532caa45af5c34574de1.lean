import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_127418 (f : ℝ → ℝ) (hf : f = λ x => 2 + logb 3 x)
  (x : ℝ) (hx : x ∈ Icc 1 9) :
  f x ^ 2 + f (x ^ 2) ∈ Icc 6 22 := by
    rw [mem_Icc] at hx
    rcases hx with ⟨hx1, hx2⟩
    have hfx : f x = 2 + logb 3 x := by rw [hf]
    have hf_x2 : f (x ^ 2) = 2 + logb 3 (x ^ 2) := by rw [hf]
    rw [mem_Icc]
    simp only [hfx, hf_x2]
    have h1 : logb 3 (x ^ 2) = 2 * logb 3 x := by
      simp [logb_pow]
    rw [h1]
    have h2 : 0 ≤ logb 3 x := by
      apply logb_nonneg
      all_goals linarith
    have h3 : logb 3 x ≤ 2 := by
      have h4 : logb 3 9 = 2 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      have h5 : logb 3 x ≤ logb 3 9 := by
        apply Real.logb_le_logb_of_le
        all_goals linarith
      linarith [h4, h5]
    constructor
    · -- Show that it is ≥ 6
      nlinarith [sq_nonneg (logb 3 x), sq_nonneg (logb 3 x - 2)]
    · -- Show that it is ≤ 22
      nlinarith [sq_nonneg (logb 3 x), sq_nonneg (logb 3 x - 2)]