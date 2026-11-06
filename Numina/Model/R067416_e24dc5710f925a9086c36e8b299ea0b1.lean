import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_117995
  (a b α β m n : ℝ)
  (h : ∀ x, 3 * x = (x - 2 / 3) + (x + 1) + (x - 1 / 3)) :
  (3 * a + 3 * α + 3 * m - 14) / 9 = (a - 4 / 3) / 3 + (α - 3) / 3 + (m - 1 / 3) / 3 := by 
  ring