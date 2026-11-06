import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

/- 26.16. Prove that the function $f(x)$, continuous on the interval $[a, b]$, is bounded on this interval, i.e., the set of all values $f(x)$ for $x$ in the interval $[a, b]$ is a bounded set. -/
theorem calculus_228554
  (f : ℝ → ℝ) (a b : ℝ) (ha : a < b)
  (hf : ContinuousOn f (Set.Icc a b)) :
  Bornology.IsBounded (Set.image f (Set.Icc a b)) := by
  -- Show that the image of a closed interval under a continuous function is another interval
  rw [ContinuousOn.image_Icc (by linarith) hf]
  -- Show that intervals are bounded
  exact Metric.isBounded_Icc (sInf (f '' Set.Icc a b)) (sSup (f '' Set.Icc a b))