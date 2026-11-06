import Mathlib

open Finset

theorem number_theory_126984 : ∏ i ∈ Icc 1 99, i < 50^99 := by
  native_decide