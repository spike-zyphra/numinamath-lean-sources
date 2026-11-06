import Mathlib

open Finset

theorem number_theory_1377 : (∏ i ∈ range 501, (4 * i + 3)) % 1000 = 875 := by
  native_decide