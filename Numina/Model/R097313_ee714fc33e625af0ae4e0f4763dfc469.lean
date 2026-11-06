import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_143745 {α : ℝ} (hα : α = π / 6) (t1 t2 : ℝ)
  (ht1 : t1 > 0) (ht2 : t2 > 0) (g : ℝ) (hg : g > 0) :
  let h := √3 / 2 * (t2 ^ 2 - t1 ^ 2)
  let d := (t2 + t1) ^ 2 / 8
  h = √3 / 2 * (t2 ^ 2 - t1 ^ 2) ∧ d = (t2 + t1) ^ 2 / 8 := by 
  constructor <;> rfl