import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_279336 {b : ℝ} (hb : b > 0 ∧ b ≠ 1) (a : ℝ) (ha : 0 < a) :
  ContinuousAt (λ x => Real.logb b x) a := by 
  have h1 : b > 0 := hb.1
  have h2 : b ≠ 1 := hb.2
  apply Real.continuousAt_logb
  all_goals
    try linarith
    try tauto