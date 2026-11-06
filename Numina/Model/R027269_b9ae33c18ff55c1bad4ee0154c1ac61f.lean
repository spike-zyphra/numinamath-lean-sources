import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_209901 (H : ℝ → ℝ)
  (hH : H = λ t => 3 * sin (8 * t / 60) + 1) :
  ∃ t, H t = 1.5 := by 
  use (Real.arcsin (1 / 6) ) * (60 / 8)
  rw [hH]
  have h1 : sin (8 * ((Real.arcsin (1 / 6)) * (60 / 8)) / 60) = 1 / 6 := by 
    have h2 : 8 * ((Real.arcsin (1 / 6)) * (60 / 8)) / 60 = Real.arcsin (1 / 6) := by 
      ring_nf
    rw [h2]
    have h3 : sin (Real.arcsin (1 / 6)) = 1 / 6 := by 
      apply Real.sin_arcsin 
      all_goals norm_num 
    linarith
  simp_all [h1]
  <;> norm_num