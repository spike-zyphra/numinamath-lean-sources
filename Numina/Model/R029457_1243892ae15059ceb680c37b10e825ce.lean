import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem inequalities_207512 (f g : ℝ → ℝ) :
  ∃ x y, 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 ∧ |f x + g y - x * y| ≥ 1 / 4 := by
  by_contra h 
  push_neg at h 
  have h1 : ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → |f x + g y - x * y| < 1 / 4 := by
    simpa using h 
  have h2 := h1 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h3 := h1 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h4 := h1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h5 := h1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h6 : -1/4 < f 0 + g 0 := by 
    cases' abs_lt.mp h2 with h7 h8
    linarith 
  have h7 : f 0 + g 0 < 1/4 := by 
    cases' abs_lt.mp h2 with h8 h9
    linarith 
  have h8 : -1/4 < f 0 + g 1 := by 
    cases' abs_lt.mp h3 with h9 h10
    linarith 
  have h9 : f 0 + g 1 < 1/4 := by 
    cases' abs_lt.mp h3 with h10 h11
    linarith 
  have h10 : -1/4 < f 1 + g 0 := by 
    cases' abs_lt.mp h4 with h11 h12
    linarith 
  have h11 : f 1 + g 0 < 1/4 := by 
    cases' abs_lt.mp h4 with h12 h13
    linarith 
  have h12 : -1/4 < f 1 + g 1 - (1 : ℝ) := by 
    cases' abs_lt.mp h5 with h13 h14
    linarith 
  have h13 : f 1 + g 1 - (1 : ℝ) < 1/4 := by 
    cases' abs_lt.mp h5 with h14 h15
    linarith 
  linarith