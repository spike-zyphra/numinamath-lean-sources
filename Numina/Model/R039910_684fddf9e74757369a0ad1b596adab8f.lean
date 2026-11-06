import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_22447 :
  IsLeast {z : ℝ | ∃ x y, x ∈ Icc (-5) (-3) ∧ y ∈ Icc 2 4 ∧ z = (x + y) / (x - y)} (-1 / 7) := by
  constructor
  · -- Show that -1/7 is in the set
    use -3, 4
    constructor
    · norm_num [mem_Icc]
    constructor
    · norm_num [mem_Icc]
    · norm_num
  · -- Show that -1/7 is the least in the set
    intro z h
    rcases h with ⟨x, y, hx, hy, hz⟩
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    have h1 : x - y ≤ -5 := by 
      linarith
    have h2 : x - y < 0 := by
      linarith
    have h3 : 8 * x + 6 * y ≤ 0 := by 
      nlinarith
    have h4 : (x + y) / (x - y) ≥ -1 / 7 := by
      apply (le_div_iff_of_neg' (by linarith)).mpr
      nlinarith
    linarith [hz, h4]