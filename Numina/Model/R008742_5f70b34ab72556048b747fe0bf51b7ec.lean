import Mathlib

open Finset Real Nat
theorem number_theory_608524: ∑ k ∈ Icc 1 2009, k * (2009 / k - 2008 / k) = 2394 := by
  native_decide