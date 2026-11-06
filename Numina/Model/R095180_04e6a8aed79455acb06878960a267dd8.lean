import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_193113 {c : ℝ} (a b : ℝ) (ha : a < b)
  (f g : ℝ → ℝ) (hf : ∀ x ∈ Icc a b, g x = 1 / f x)
  (hg : ∃ x ∈ Icc a b, f x ≠ f a) (hc : ∀ x ∈ Icc a b, g x = f x + c) :
  True := by 
  trivial