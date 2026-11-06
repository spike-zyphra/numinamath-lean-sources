import Mathlib

open Real Set
open scoped Real

theorem algebra_170357 (x : ℝ) (hx : x ∈ Icc (-π/12) (-π/3)) :
    IsGreatest {y | ∃ x : ℝ, x ∈ Icc (-π/12) (-π/3) ∧ y = tan (x + 2*π/3) + tan (x + π/6) + cos (x + π/6)} (11*sqrt 3/6) := by
  exfalso
  rcases mem_Icc.mp hx with ⟨h2, h3⟩
  have h4 : -π/12 > -π/3 := by
    linarith [Real.pi_pos]
  linarith