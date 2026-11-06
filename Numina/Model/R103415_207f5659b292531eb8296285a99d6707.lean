import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_164451 : ∫ x in (0)..(π/2), cos x = 1 := by 
  norm_num [Real.sin_pi_div_two, Real.sin_zero]