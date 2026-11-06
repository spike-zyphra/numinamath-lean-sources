import Mathlib

theorem number_theory_2448 (x : ℕ) (hx : x = 1993) : ∑ i ∈ Finset.Icc 1900 x, ⌊Real.sqrt i⌋ = 4100 := by 
  subst hx
  norm_num [Finset.sum_Icc_succ_top, Int.floor_eq_iff]
  <;> ring_nf
  <;> norm_num
  <;> ring
  <;> norm_num