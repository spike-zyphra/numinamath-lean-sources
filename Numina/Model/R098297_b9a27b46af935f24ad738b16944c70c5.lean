import Mathlib

open Finset

theorem algebra_105891 : ∏ i ∈ range 1995, ((i + 1) * (i + 2)) / (1 + (i + 1) * (i + 2)) = (998 * 1995 - 1) / (998 * 1995 + 1) := by 
  native_decide