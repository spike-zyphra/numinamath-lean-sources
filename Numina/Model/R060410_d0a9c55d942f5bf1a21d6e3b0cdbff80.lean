import Mathlib

open Real Set
open scoped Real

theorem inequalities_288101 (x : ℝ) (hx : x ∈ Ioo 0 (π / 2) ∪ Ioo (-π / 2) 0) :
    0 ≤ abs (sin (2 * x) * cos x * cos x + cos x * sin (2 * x) * cos x + cos x * cos x * sin (2 * x)) := by
  apply abs_nonneg