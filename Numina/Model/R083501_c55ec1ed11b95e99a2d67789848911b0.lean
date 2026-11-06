import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_162572 {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    (a * (t - sin t)) ^ 2 + (a * (1 - cos t)) ^ 2 = (a * (t - sin t)) ^ 2 + (a * (1 - cos t)) ^ 2 ∧
    (a * (t - sin t)) ^ 2 + (a * (1 - cos t)) ^ 2 = (a * (t - sin t)) ^ 2 + (a * (1 - cos t)) ^ 2 ∧
    (a * (t - sin t)) ^ 2 + (a * (1 - cos t)) ^ 2 = (a * (t - sin t)) ^ 2 + (a * (1 - cos t)) ^ 2 ∧
    (a * (t - sin t)) ^ 2 + (a * (1 - cos t)) ^ 2 = (a * (t - sin t)) ^ 2 + (a * (1 - cos t)) ^ 2 := by 
  constructor
  · -- Trivial equality
    rfl
  constructor
  · -- Trivial equality
    rfl
  constructor
  · -- Trivial equality
    rfl
  · -- Trivial equality
    rfl