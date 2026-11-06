import Mathlib
open Finset

theorem algebra_1375 : (∑ i ∈ range 2006, (i + 1)) / ∏ i ∈ range 1003, (1 - 1 / ((1004 + i) : ℝ)) = 4026042 := by
  have h1 : (∑ i ∈ range 2006, (i + 1 : ℝ)) = (2006 * 2007 : ℝ) / 2 := by
    norm_num [sum_range_succ]
  have h2 : (∏ i ∈ range 1003, (1 - 1 / (1004 + (i : ℝ)) : ℝ)) = (1003 : ℝ) / 2006 := by
    norm_num [prod_range_succ]
  field_simp [h1, h2]
  <;> norm_num