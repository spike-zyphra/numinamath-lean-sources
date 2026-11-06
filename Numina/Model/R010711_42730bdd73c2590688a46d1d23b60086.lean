import Mathlib
open Mathlib
lemma algebra_1141 : (∑ k in Finset.range 2003, 2 * (k + 1)) - (∑ k in Finset.range 2003, (2 * k + 1)) = 2003 := by
  native_decide