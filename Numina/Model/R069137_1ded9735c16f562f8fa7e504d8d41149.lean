import Mathlib

open Finset

theorem number_theory_2159 : 1993 ∣ (∏ i ∈ range 996, (2 * (i + 1)) - ∏ i ∈ range 996, (2 * i + 1)) := by 
  native_decide