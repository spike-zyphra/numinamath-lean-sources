import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_146191 (f : ℂ → ℂ) (hf : f = λ z => z ^ 2) :
  Continuous f := by
  rw [hf]
  apply Continuous.pow
  exact continuous_id