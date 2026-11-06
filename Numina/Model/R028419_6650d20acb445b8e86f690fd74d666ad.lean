import Mathlib

open Real
open scoped BigOperators

theorem inequalities_200915 :
  IsLeast {x | ∑ i in Finset.range 2001, (2 : ℕ)^(x + i) > 2^2017} 17 := by
  constructor
  · -- Show 17 is in the set
    native_decide
  · -- Show there is no smaller element in the set
    intro x h
    have h1 : ∑ i in Finset.range 2001, (2 : ℕ)^(x + i) > 2^2017 := h
    by_contra h2
    push_neg at h2
    have h2' : x ≤ 16 := by omega
    have h3 : ∑ i in Finset.range 2001, (2 : ℕ)^(x + i) ≤ 2^2017 := by
      interval_cases x <;> native_decide
    linarith