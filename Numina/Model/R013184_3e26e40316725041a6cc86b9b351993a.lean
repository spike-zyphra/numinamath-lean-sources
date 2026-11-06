import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_253826 (a : ℝ) :
  {x : ℝ | a * x ^ 2 - abs (x + 1) + 2 * a < 0} = ∅ ↔
  a ≥ (sqrt 3 + 1) / 4 := by
  simp [Set.eq_empty_iff_forall_not_mem, Set.mem_setOf_eq]
  constructor
  · -- Assume that {x | a x² - |x+1| + 2a < 0} = ∅, prove a ≥ (sqrt 3 + 1)/4
    intro h
    by_contra h1
    push_neg at h1
    -- Let's show that for x = -1 + Real.sqrt 3, the inequality is < 0
    have h2 : a * (-1 + Real.sqrt 3) ^ 2 - abs ((-1 + Real.sqrt 3) + 1) + 2 * a < (0 : ℝ) := by
      have h3 : abs ((-1 + Real.sqrt 3) + 1 : ℝ) = Real.sqrt 3 := by
        have h4 : (-1 + Real.sqrt 3 : ℝ) + 1 = Real.sqrt 3 := by
          ring
        rw [h4]
        simp
      rw [h3]
      nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg (a - (Real.sqrt 3 + 1) / 4), Real.sqrt_nonneg 3]
    -- This contradicts h, which states that for all x, a * x ^ 2 - abs (x + 1) + 2 * a ≥ 0
    specialize h (-1 + Real.sqrt 3)
    linarith
  · -- Assume a ≥ (sqrt 3 + 1) / 4, prove {x | a * x ^ 2 - abs (x + 1) + 2 * a < 0} = ∅
    intro h x
    have h1 : a * x ^ 2 - abs (x + 1) + 2 * a ≥ 0 := by
      by_cases h2 : x ≥ -1
      · -- x >= -1, so |x+1|=x+1
        rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith)]
        nlinarith [sq_nonneg (x * a - (1 / 2) * a), sq_nonneg (x - (-1 + Real.sqrt 3)), sq_nonneg (x - (-1 - Real.sqrt 3)), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg (a - (Real.sqrt 3 + 1) / 4), h, Real.sqrt_nonneg 3]
      · -- x < -1, so |x+1|=-(x+1)
        rw [abs_of_neg (show x + 1 < 0 by linarith)]
        nlinarith [sq_nonneg (x * a - (-1 / 2) * a), sq_nonneg (x - (-1 - Real.sqrt 3)), sq_nonneg (x - (-1 + Real.sqrt 3)), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg (a - (Real.sqrt 3 + 1) / 4), h, Real.sqrt_nonneg 3]
    linarith