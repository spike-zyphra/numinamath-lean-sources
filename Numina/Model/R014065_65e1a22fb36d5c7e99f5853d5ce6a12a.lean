import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_78258
  (f g : ℝ → ℝ)
  (hf : Continuous f)
  (hg : Continuous g)
  (hpos : ∀ x, f x > 0 ∧ g x > 0)
  (hf' : ∀ x, g x = ∫ t in (0)..x, f t)
  (hf'' : ∀ x, (f x)^2 - (g x)^2 = 1) :
  (∀ x, f x = Real.cosh x) ∨ (∀ x, f x = -Real.cosh x) := by
  have h3 : g 0 = 0 := by
    specialize hf' 0 
    norm_num at hf'
    all_goals linarith
  have h4 : g 0 > 0 := by 
    have h3 := hpos 0
    linarith 
  linarith