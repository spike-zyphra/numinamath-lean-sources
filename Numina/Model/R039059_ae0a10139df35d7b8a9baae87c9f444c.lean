import Mathlib

open Real Set

theorem algebra_16956 :
    IsGreatest {x ^ 4 / (x ^ 8 + 2 * x ^ 6 - 4 * x ^ 4 + 8 * x ^ 2 + 16) | (x : ℝ) (_ : x ^ 8 + 2 * x ^ 6 - 4 * x ^ 4 + 8 * x ^ 2 + 16 ≠ 0)} (1 / 12) := by
  constructor
  · -- Show that 1/12 is in the set
    use Real.sqrt 2
    have h1 : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h2 : (Real.sqrt (2 : ℝ)) ^ 4 = 4 := by
      calc
        (Real.sqrt (2 : ℝ)) ^ 4 = ((Real.sqrt (2 : ℝ)) ^ 2) ^ 2 := by ring
        _ = 2 ^ 2 := by rw [h1]
        _ = (4 : ℝ) := by norm_num
    have h3 : (Real.sqrt (2 : ℝ)) ^ 6 = 8 := by
      calc
        (Real.sqrt (2 : ℝ)) ^ 6 = ((Real.sqrt (2 : ℝ)) ^ 2) ^ 3 := by ring
        _ = 2 ^ 3 := by rw [h1]
        _ = (8 : ℝ) := by norm_num
    have h4 : (Real.sqrt (2 : ℝ)) ^ 8 = 16 := by
      calc
        (Real.sqrt (2 : ℝ)) ^ 8 = ((Real.sqrt (2 : ℝ)) ^ 2) ^ 4 := by ring
        _ = 2 ^ 4 := by rw [h1]
        _ = (16 : ℝ) := by norm_num
    simp_all [h1, h2, h3, h4]
    all_goals norm_num
  · -- Show that 1/12 is the greatest
    intro y hy
    rcases hy with ⟨x, hxne, hx⟩
    have h1 : x ^ 8 + 2 * x ^ 6 - 4 * x ^ 4 + 8 * x ^ 2 + 16 > 0 := by
      nlinarith [sq_nonneg (x ^ 4), sq_nonneg (x ^ 3), sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 2 + 2), sq_nonneg (x ^ 2 - 4), sq_nonneg (x + 2), sq_nonneg (x - 2), sq_nonneg (x ^ 2), sq_nonneg (x ^ 6), sq_nonneg (x ^ 4 - 2 * x ^ 2), sq_nonneg (x ^ 4 + 2 * x ^ 2)]
    have h2 : x ^ 4 ≤ (1 / 12) * (x ^ 8 + 2 * x ^ 6 - 4 * x ^ 4 + 8 * x ^ 2 + 16) := by
      nlinarith [sq_nonneg (x ^ 4 - 4), sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 2 + 2), sq_nonneg (x ^ 2 - 4), sq_nonneg (x ^ 2), sq_nonneg (x ^ 6 - x ^ 4), sq_nonneg (x ^ 4 - 2 * x ^ 2), sq_nonneg (x ^ 4 + 2 * x ^ 2 - 4), sq_nonneg (x + 2), sq_nonneg (x - 2)]
    have h3 : x ^ 4 / (x ^ 8 + 2 * x ^ 6 - 4 * x ^ 4 + 8 * x ^ 2 + 16) ≤ (1 / 12) := by
      have h4 : x ^ 8 + 2 * x ^ 6 - 4 * x ^ 4 + 8 * x ^ 2 + 16 > 0 := h1
      apply (div_le_iff₀ h4).mpr
      linarith [h2]
    linarith [h3, hx]