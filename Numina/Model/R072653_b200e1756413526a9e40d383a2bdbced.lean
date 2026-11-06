import Mathlib

open Finset

theorem number_theory_30785 : (∏ i ∈ range 1006, (2 * i + 1)) % 1000 = 875 := by 
  native_decide