import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_319635 :
  IsGreatest {t : ℝ | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ x < 1 ∧ y < 1 ∧ t = x * y * (1 - x - y) / ((x + y) * (1 - x) * (1 - y))} (1 / 8) := by 
  constructor
  · -- Show 1/8 is in the set
    use 1 / 3, 1 / 3
    norm_num
  · -- Show 1/8 is greatest
    intro t ht
    rcases ht with ⟨x, y, hx1, hy1, hx2, hy2, ht⟩
    have h1 : 0 < x + y := by linarith
    have h2 : 0 < 1 - x := by linarith
    have h3 : 0 < 1 - y := by linarith
    have h4 : 0 < (x + y) * (1 - x) * (1 - y) := by positivity
    have h5 : x * y * (1 - x - y) ≤ (1 / 8) * ((x + y) * (1 - x) * (1 - y)) := by
      have h6 : 8 * (x * y * (1 - x - y)) ≤ (x + y) * (1 - x) * (1 - y) := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_nonneg (x + y - 4/3), sq_nonneg (x * y - 1/9), sq_nonneg (x + y - 2/3), sq_nonneg (x * (y - 1/3)), sq_nonneg (y * (x - 1/3)), 
          mul_pos hx1 hy1, 
          mul_pos hx1 (show 0 < 1 - x by linarith), 
          mul_pos hy1 (show 0 < 1 - y by linarith), 
          mul_pos (show 0 < 1 - x by linarith) (show 0 < 1 - y by linarith), 
          mul_nonneg (mul_nonneg (le_of_lt hx1) (le_of_lt hy1)) (mul_nonneg (le_of_lt (show 0 < 1 - x by linarith)) (le_of_lt (show 0 < 1 - y by linarith)))]
      linarith
    have h6' : x * y * (1 - x - y) / ((x + y) * (1 - x) * (1 - y)) ≤ 1 / 8 := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      linarith [h5]
    linarith [ht, h6']