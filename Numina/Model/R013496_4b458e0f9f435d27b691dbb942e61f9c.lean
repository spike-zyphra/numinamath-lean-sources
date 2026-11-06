import Mathlib

open Real

theorem calculus_64342 :
    IsLeast {n | ∑ i ∈ Finset.Icc 1 n, i * 3 ^ i > 3 ^ 2007} 2000 := by
  constructor
  · -- Show that 2000 is in the set
    native_decide
  · -- Show that 2000 is minimal
    intro n hn
    have : ∑ i ∈ Finset.Icc 1 n, i * 3 ^ i > 3 ^ 2007 := by
      simpa using hn
    by_contra h
    push_neg at h
    have h1 : n ≤ 1999 := by omega
    have h2 : ∑ i ∈ Finset.Icc 1 n, i * 3 ^ i ≤ 3 ^ 2007 := by
      interval_cases n <;> native_decide
    linarith