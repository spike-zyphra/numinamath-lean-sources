import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_149184 (a : ℝ) (ha : a > 0) :
    let Mxy := (a * (a - 0) * (a - 0)) / (3 * 2 * 1)
    let Myz := (a * (a - 0) * (a - 0)) / (3 * 2 * 1)
    let Mxz := (a * (a - 0) * (a - 0)) / (3 * 2 * 1)
    let x₀ := a / 3
    let y₀ := a / 3
    let z₀ := a / 3
    Mxy = Mxz ∧ Mxy = Myz ∧ x₀ = y₀ ∧ y₀ = z₀ := by
  constructor
  · -- Show Mxy = Mxz
    rfl 
  constructor
  · -- Show Mxy = Myz 
    rfl 
  constructor
  · -- Show x₀ = y₀ 
    rfl 
  · -- Show y₀ = z₀ 
    rfl